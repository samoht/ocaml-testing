(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*      Damien Doligez and Francois Rouaix, INRIA Rocquencourt         *)
(*          Ported to Caml Special Light by John Malecki               *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

open Printf

open Clflags
open Config
open Location
open Misc
open Parsetree

(* User programs must not use identifiers that start with these prefixes. *)
let idprefix = "__ocaml_prof_";;
let modprefix = "OCAML__prof_";;

(* Errors specific to the profiler *)
exception Profiler of string

(* Modes *)
let instr_fun    = ref false
and instr_match  = ref false
and instr_if     = ref false
and instr_loops  = ref false
and instr_try    = ref false

let cur_point = ref 0
and inchan = ref stdin
and outchan = ref stdout

(* To copy source fragments *)
let copy_buffer = String.create 256

let copy_chars_unix nchars =
  let n = ref nchars in
  while !n > 0 do
    let m = input !inchan copy_buffer 0 (min !n 256) in
    if m = 0 then raise End_of_file;
    output !outchan copy_buffer 0 m;
    n := !n - m
  done

let copy_chars_win32 nchars =
  for i = 1 to nchars do
    let c = input_char !inchan in
    if c <> '\r' then output_char !outchan c
  done

let copy_chars =
  match Sys.os_type with
    "Win32" | "Cygwin" -> copy_chars_win32
  | _       -> copy_chars_unix

let copy next =
  assert (next >= !cur_point);
  seek_in !inchan !cur_point;
  copy_chars (next - !cur_point);
  cur_point := next;
;;

let prof_counter = ref 0;;

let instr_mode = ref false

type insert = Open | Close;;
let to_insert = ref ([] : (insert * int) list);;

let insert_action st en =
  to_insert := (Open, st) :: (Close, en) :: !to_insert
;;

(* Producing instrumented code *)
let add_incr_counter modul (kind,pos) =
   copy pos;
   match kind with
   | Open ->
         fprintf !outchan "(%sProfiling.incr %s%s_cnt %d; "
                 modprefix idprefix modul !prof_counter;
         incr prof_counter;
   | Close -> fprintf !outchan ")";
;;

let counters = ref (Array.create 0 0)

(* User defined marker *)
let special_id = ref ""

(* Producing results of profile run *)
let add_val_counter (kind,pos) =
  if kind = Open then begin
    copy pos;
    fprintf !outchan "(* %s%d *) " !special_id !counters.(!prof_counter);
    incr prof_counter;
  end
;;

(* ************* rewrite ************* *)

let insert_profile rw_exp ex =
  let st = ex.pexp_loc.loc_start.Lexing.pos_cnum
  and en = ex.pexp_loc.loc_end.Lexing.pos_cnum
  and gh = ex.pexp_loc.loc_ghost
  in
  if gh || st = en then
    rw_exp true ex
  else begin
    insert_action st en;
    rw_exp false ex;
  end
;;


let pos_len = ref 0

let init_rewrite modes mod_name =
  cur_point := 0;
  if !instr_mode then begin
    fprintf !outchan "module %sProfiling = Profiling;; " modprefix;
    fprintf !outchan "let %s%s_cnt = Array.create 000000000" idprefix mod_name;
    pos_len := pos_out !outchan;
    fprintf !outchan
            " 0;; Profiling.counters := \
              (\"%s\", (\"%s\", %s%s_cnt)) :: !Profiling.counters;; "
            mod_name modes idprefix mod_name;
  end

let final_rewrite add_function =
  to_insert := Sort.list (fun x y -> snd x < snd y) !to_insert;
  prof_counter := 0;
  List.iter add_function !to_insert;
  copy (in_channel_length !inchan);
  if !instr_mode then begin
    let len = string_of_int !prof_counter in
    if String.length len > 9 then raise (Profiler "too many counters");
    seek_out !outchan (!pos_len - String.length len);
    output_string !outchan len
  end;
  (* Cannot close because outchan is stdout and Format doesn't like
     a closed stdout.
    close_out !outchan;
  *)
;;

let rec rewrite_patexp_list iflag l =
  rewrite_exp_list iflag (List.map snd l)

and rewrite_patlexp_list iflag l =
  rewrite_exp_list iflag (List.map snd l)

and rewrite_labelexp_list iflag l =
  rewrite_exp_list iflag (List.map snd l)

and rewrite_exp_list iflag l =
  List.iter (rewrite_exp iflag) l

and rewrite_exp iflag sexp =
  if iflag then insert_profile rw_exp sexp
           else rw_exp false sexp

and rw_exp iflag sexp =
  match sexp.pexp_desc with
    Pexp_ident lid -> ()
  | Pexp_constant cst -> ()

  | Pexp_let(_, spat_sexp_list, sbody) ->
    rewrite_patexp_list iflag spat_sexp_list;
    rewrite_exp iflag sbody

  | Pexp_function (_, _, caselist) ->
    if !instr_fun then
      rewrite_function iflag caselist
    else
      rewrite_patlexp_list iflag caselist

  | Pexp_match(sarg, caselist) ->
    rewrite_exp iflag sarg;
    if !instr_match && not sexp.pexp_loc.loc_ghost then
      rewrite_funmatching caselist
    else
      rewrite_patlexp_list iflag caselist

  | Pexp_try(sbody, caselist) ->
    rewrite_exp iflag sbody;
    if !instr_try && not sexp.pexp_loc.loc_ghost then
      rewrite_trymatching caselist
    else
      rewrite_patexp_list iflag caselist

  | Pexp_apply(sfunct, sargs) ->
    rewrite_exp iflag sfunct;
    rewrite_exp_list iflag (List.map snd sargs)

  | Pexp_tuple sexpl ->
    rewrite_exp_list iflag sexpl

  | Pexp_construct(_, None, _) -> ()
  | Pexp_construct(_, Some sarg, _) ->
    rewrite_exp iflag sarg

  | Pexp_variant(_, None) -> ()
  | Pexp_variant(_, Some sarg) ->
    rewrite_exp iflag sarg

  | Pexp_record(lid_sexp_list, None) ->
    rewrite_labelexp_list iflag lid_sexp_list
  | Pexp_record(lid_sexp_list, Some sexp) ->
    rewrite_exp iflag sexp;
    rewrite_labelexp_list iflag lid_sexp_list

  | Pexp_field(sarg, _) ->
    rewrite_exp iflag sarg

  | Pexp_setfield(srecord, _, snewval) ->
    rewrite_exp iflag srecord;
    rewrite_exp iflag snewval

  | Pexp_array(sargl) ->
    rewrite_exp_list iflag sargl

  | Pexp_ifthenelse(scond, sifso, None) ->
      rewrite_exp iflag scond;
      rewrite_ifbody iflag sexp.pexp_loc.loc_ghost sifso
  | Pexp_ifthenelse(scond, sifso, Some sifnot) ->
      rewrite_exp iflag scond;
      rewrite_ifbody iflag sexp.pexp_loc.loc_ghost sifso;
      rewrite_ifbody iflag sexp.pexp_loc.loc_ghost sifnot

  | Pexp_sequence(sexp1, sexp2) ->
    rewrite_exp iflag sexp1;
    rewrite_exp iflag sexp2

  | Pexp_while(scond, sbody) ->
    rewrite_exp iflag scond;
    if !instr_loops && not sexp.pexp_loc.loc_ghost
    then insert_profile rw_exp sbody
    else rewrite_exp iflag sbody

  | Pexp_for(_, slow, shigh, _, sbody) ->
    rewrite_exp iflag slow;
    rewrite_exp iflag shigh;
    if !instr_loops && not sexp.pexp_loc.loc_ghost
    then insert_profile rw_exp sbody
    else rewrite_exp iflag sbody

  | Pexp_constraint(sarg, _, _) ->
    rewrite_exp iflag sarg

  | Pexp_when(scond, sbody) ->
    rewrite_exp iflag scond;
    rewrite_exp iflag sbody

  | Pexp_send (sobj, _) ->
    rewrite_exp iflag sobj

  | Pexp_new _ -> ()

  | Pexp_setinstvar (_, sarg) ->
    rewrite_exp iflag sarg

  | Pexp_override l ->
      List.iter (fun (_, sexp) -> rewrite_exp iflag sexp) l

  | Pexp_letmodule (_, smod, sexp) ->
      rewrite_mod iflag smod;
      rewrite_exp iflag sexp

  | Pexp_assert (cond) -> rewrite_exp iflag cond
  | Pexp_assertfalse -> ()

  | Pexp_lazy (expr) -> rewrite_exp iflag expr

  | Pexp_poly (sexp, _) -> rewrite_exp iflag sexp

  | Pexp_object (_, fieldl) ->
      List.iter (rewrite_class_field iflag) fieldl

  | Pexp_newtype (_, sexp) -> rewrite_exp iflag sexp
  | Pexp_open (_, e) -> rewrite_exp iflag e
  | Pexp_pack (smod) -> rewrite_mod iflag smod

and rewrite_ifbody iflag ghost sifbody =
  if !instr_if && not ghost then
    insert_profile rw_exp sifbody
  else
    rewrite_exp iflag sifbody

(* called only when !instr_fun *)
and rewrite_annotate_exp_list l =
  List.iter
    (function
     | {pexp_desc = Pexp_when(scond, sbody)}
        -> insert_profile rw_exp scond;
           insert_profile rw_exp sbody;
     | {pexp_desc = Pexp_constraint(sbody, _, _)} (* let f x : t = e *)
        -> insert_profile rw_exp sbody
     | sexp -> insert_profile rw_exp sexp)
    l

and rewrite_function iflag = function
  | [spat, ({pexp_desc = Pexp_function _} as sexp)] -> rewrite_exp iflag sexp
  | l -> rewrite_funmatching l

and rewrite_funmatching l =
  rewrite_annotate_exp_list (List.map snd l)

and rewrite_trymatching l =
  rewrite_annotate_exp_list (List.map snd l)

(* Rewrite a class definition *)

and rewrite_class_field iflag =
  function
    Pcf_inher (_, cexpr, _)     -> rewrite_class_expr iflag cexpr
  | Pcf_val (_, _, _, sexp, _)  -> rewrite_exp iflag sexp
  | Pcf_meth (_, _, _, ({pexp_desc = Pexp_function _} as sexp), _) ->
      rewrite_exp iflag sexp
  | Pcf_meth (_, _, _, sexp, loc) ->
      if !instr_fun && not loc.loc_ghost then insert_profile rw_exp sexp
      else rewrite_exp iflag sexp
  | Pcf_let(_, spat_sexp_list, _) ->
      rewrite_patexp_list iflag spat_sexp_list
  | Pcf_init sexp ->
      rewrite_exp iflag sexp
  | Pcf_valvirt _ | Pcf_virt _ | Pcf_cstr _  -> ()

and rewrite_class_expr iflag cexpr =
  match cexpr.pcl_desc with
    Pcl_constr _ -> ()
  | Pcl_structure (_, fields) ->
      List.iter (rewrite_class_field iflag) fields
  | Pcl_fun (_, _, _, cexpr) ->
      rewrite_class_expr iflag cexpr
  | Pcl_apply (cexpr, exprs) ->
      rewrite_class_expr iflag cexpr;
      List.iter (rewrite_exp iflag) (List.map snd exprs)
  | Pcl_let (_, spat_sexp_list, cexpr) ->
      rewrite_patexp_list iflag spat_sexp_list;
      rewrite_class_expr iflag cexpr
  | Pcl_constraint (cexpr, _) ->
      rewrite_class_expr iflag cexpr

and rewrite_class_declaration iflag cl =
  rewrite_class_expr iflag cl.pci_expr

(* Rewrite a module expression or structure expression *)

and rewrite_mod iflag smod =
  match smod.pmod_desc with
    Pmod_ident lid -> ()
  | Pmod_structure sstr -> List.iter (rewrite_str_item iflag) sstr
  | Pmod_functor(param, smty, sbody) -> rewrite_mod iflag sbody
  | Pmod_apply(smod1, smod2) -> rewrite_mod iflag smod1; rewrite_mod iflag smod2
  | Pmod_constraint(smod, smty) -> rewrite_mod iflag smod
  | Pmod_unpack(sexp) -> rewrite_exp iflag sexp

and rewrite_str_item iflag item =
  match item.pstr_desc with
    Pstr_eval exp -> rewrite_exp iflag exp
  | Pstr_value(_, exps)
     -> List.iter (function (_,exp) -> rewrite_exp iflag exp) exps
  | Pstr_module(name, smod) -> rewrite_mod iflag smod
  | Pstr_class classes -> List.iter (rewrite_class_declaration iflag) classes
  | _ -> ()

(* Rewrite a .ml file *)
let rewrite_file srcfile add_function =
  inchan := open_in_bin srcfile;
  let lb = Lexing.from_channel !inchan in
  Location.input_name := srcfile;
  Location.init lb srcfile;
  List.iter (rewrite_str_item false) (Parse.implementation lb);
  final_rewrite add_function;
  close_in !inchan

(* Copy a non-.ml file without change *)
let null_rewrite srcfile =
  inchan := open_in_bin srcfile;
  copy (in_channel_length !inchan);
  close_in !inchan
;;

(* Setting flags from saved config *)
let set_flags s =
  for i = 0 to String.length s - 1 do
    match String.get s i with
      'f' -> instr_fun := true
    | 'm' -> instr_match := true
    | 'i' -> instr_if := true
    | 'l' -> instr_loops := true
    | 't' -> instr_try := true
    | 'a' -> instr_fun := true; instr_match := true;
             instr_if := true; instr_loops := true;
             instr_try := true
    | _ -> ()
    done

(* Command-line options *)

let modes = ref "fm"
let dumpfile = ref "ocamlprof.dump"

(* Process a file *)

let process_intf_file filename = null_rewrite filename;;

let process_impl_file filename =
   let modname = Filename.basename(Filename.chop_extension filename) in
       (* FIXME should let modname = String.capitalize modname *)
   if !instr_mode then begin
     (* Instrumentation mode *)
     set_flags !modes;
     init_rewrite !modes modname;
     rewrite_file filename (add_incr_counter modname);
   end else begin
     (* Results mode *)
     let ic = open_in_bin !dumpfile in
     let allcounters =
       (input_value ic : (string * (string * int array)) list) in
     close_in ic;
     let (modes, cv) =
       try
         List.assoc modname allcounters
       with Not_found ->
         raise(Profiler("Module " ^ modname ^ " not used in this profile."))
     in
     counters := cv;
     set_flags modes;
     init_rewrite modes modname;
     rewrite_file filename add_val_counter;
   end
;;

let process_anon_file filename =
  if Filename.check_suffix filename ".ml" then
    process_impl_file filename
  else
    process_intf_file filename
;;

(* Main function *)

open Format

let usage = "Usage: ocamlprof <options> <files>\noptions are:"

let print_version () =
  printf "ocamlprof, version %s@." Sys.ocaml_version;
  exit 0;
;;

let print_version_num () =
  printf "%s@." Sys.ocaml_version;
  exit 0;
;;

let main () =
  try
    Warnings.parse_options false "a";
    Arg.parse [
       "-f", Arg.String (fun s -> dumpfile := s),
             "<file>     Use <file> as dump file (default ocamlprof.dump)";
       "-F", Arg.String (fun s -> special_id := s),
             "<s>        Insert string <s> with the counts";
       "-impl", Arg.String process_impl_file,
                "<file>  Process <file> as a .ml file";
       "-instrument", Arg.Set instr_mode, "  (undocumented)";
       "-intf", Arg.String process_intf_file,
                "<file>  Process <file> as a .mli file";
       "-m", Arg.String (fun s -> modes := s), "<flags>    (undocumented)";
       "-version", Arg.Unit print_version,
                   "     Print version and exit";
       "-vnum", Arg.Unit print_version_num,
                "        Print version number and exit";
      ] process_anon_file usage;
    exit 0
  with x ->
    let report_error ppf = function
    | Lexer.Error(err, range) ->
        fprintf ppf "@[%a%a@]@."
        Location.print_error range  Lexer.report_error err
    | Syntaxerr.Error err ->
        fprintf ppf "@[%a@]@."
        Syntaxerr.report_error err
    | Profiler msg ->
        fprintf ppf "@[%s@]@." msg
    | Sys_error msg ->
        fprintf ppf "@[I/O error:@ %s@]@." msg
    | x -> raise x in
    report_error Format.err_formatter x;
    exit 2

let _ = main ()
