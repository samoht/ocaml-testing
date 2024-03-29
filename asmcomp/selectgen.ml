(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Selection of pseudo-instructions, assignment of pseudo-registers,
   sequentialization. *)

open Misc
open Cmm
open Reg
open Mach
open Debuginfo

type environment = (Ident.t, Reg.t array) Tbl.t

(* Infer the type of the result of an operation *)

let oper_result_type = function
    Capply ty -> ty
  | Cextcall(s, ty, alloc) -> ty
  | Cload c ->
      begin match c with
        Word -> typ_addr
      | Single | Double | Double_u -> typ_float
      | _ -> typ_int
      end
  | Calloc -> typ_addr
  | Cstore c -> typ_void
  | Caddi | Csubi | Cmuli | Cdivi | Cmodi |
    Cand | Cor | Cxor | Clsl | Clsr | Casr |
    Ccmpi _ | Ccmpa _ | Ccmpf _ -> typ_int
  | Cadda | Csuba -> typ_addr
  | Cnegf | Cabsf | Caddf | Csubf | Cmulf | Cdivf -> typ_float
  | Cfloatofint -> typ_float
  | Cintoffloat -> typ_int
  | Craise -> typ_void
  | Ccheckbound -> typ_void

(* Infer the size in bytes of the result of a simple expression *)

let size_expr env exp =
  let rec size localenv c = match c.exp with
      Cconst_int _ | Cconst_natint _ -> Arch.size_int
    | Cconst_symbol _ | Cconst_pointer _ | Cconst_natpointer _ ->
        Arch.size_addr
    | Cconst_float _ -> Arch.size_float
    | Cvar id ->
        begin try
          Tbl.find id localenv
        with Not_found ->
        try
          let regs = Tbl.find id env in
          size_machtype (Array.map (fun r -> r.typ) regs)
        with Not_found ->
          fatal_error("Selection.size_expr: unbound var " ^
                      Ident.unique_name id)
        end
    | Ctuple el ->
        List.fold_right (fun e sz -> size localenv e + sz) el 0
    | Cop(op, args) ->
        size_machtype(oper_result_type op)
    | Clet(id, arg, body) ->
        size (Tbl.add id (size localenv arg) localenv) body
    | Csequence(e1, e2) ->
        size localenv e2
    | _ ->
        fatal_error "Selection.size_expr"
  in size Tbl.empty exp

(* Swap the two arguments of an integer comparison *)

let swap_intcomp = function
    Isigned cmp -> Isigned(swap_comparison cmp)
  | Iunsigned cmp -> Iunsigned(swap_comparison cmp)

(* Naming of registers *)

let all_regs_anonymous rv =
  try
    for i = 0 to Array.length rv - 1 do
      if String.length rv.(i).name > 0 then raise Exit
    done;
    true
  with Exit ->
    false

let name_regs id rv =
  if Array.length rv = 1 then
    rv.(0).name <- Ident.name id
  else
    for i = 0 to Array.length rv - 1 do
      rv.(i).name <- Ident.name id ^ "#" ^ string_of_int i
    done

(* "Join" two instruction sequences, making sure they return their results
   in the same registers. *)

let join opt_r1 seq1 opt_r2 seq2 =
  let dbg = Debuginfo.none in
  match (opt_r1, opt_r2) with
    (None, _) -> opt_r2
  | (_, None) -> opt_r1
  | (Some r1, Some r2) ->
      let l1 = Array.length r1 in
      assert (l1 = Array.length r2);
      let r = Array.create l1 Reg.dummy in
      for i = 0 to l1-1 do
        if String.length r1.(i).name = 0 then begin
          r.(i) <- r1.(i);
          seq2#insert_move dbg r2.(i) r1.(i)
        end else if String.length r2.(i).name = 0 then begin
          r.(i) <- r2.(i);
          seq1#insert_move dbg r1.(i) r2.(i)
        end else begin
          r.(i) <- Reg.create r1.(i).typ;
          seq1#insert_move dbg r1.(i) r.(i);
          seq2#insert_move dbg r2.(i) r.(i)
        end
      done;
      Some r

(* Same, for N branches *)

let join_array rs =
  let some_res = ref None in
  for i = 0 to Array.length rs - 1 do
    let (r, s) = rs.(i) in
    if r <> None then some_res := r
  done;
  match !some_res with
    None -> None
  | Some template ->
      let size_res = Array.length template in
      let res = Array.create size_res Reg.dummy in
      for i = 0 to size_res - 1 do
        res.(i) <- Reg.create template.(i).typ
      done;
      for i = 0 to Array.length rs - 1 do
        let (r, s) = rs.(i) in
        match r with
          None -> ()
        | Some r -> s#insert_moves Debuginfo.none r res
      done;
      Some res

(* Registers for catch constructs *)
let catch_regs = ref []

(* Name of function being compiled *)
let current_function_name = ref ""

(* The default instruction selection class *)

class virtual selector_generic = object (self)

(* Says if an expression is "simple". A "simple" expression has no
   side-effects and its execution can be delayed until its value
   is really needed. In the case of e.g. an [alloc] instruction,
   the non-simple arguments are computed in right-to-left order
   first, then the block is allocated, then the simple arguments are
   evaluated and stored. *)

method is_simple_expr c = match c.exp with
    Cconst_int _ -> true
  | Cconst_natint _ -> true
  | Cconst_float _ -> true
  | Cconst_symbol _ -> true
  | Cconst_pointer _ -> true
  | Cconst_natpointer _ -> true
  | Cvar _ -> true
  | Ctuple el -> List.for_all self#is_simple_expr el
  | Clet(id, arg, body) -> self#is_simple_expr arg && self#is_simple_expr body
  | Csequence(e1, e2) -> self#is_simple_expr e1 && self#is_simple_expr e2
  | Cop(op, args) ->
      begin match op with
        (* The following may have side effects *)
      | Capply _ | Cextcall _ | Calloc | Cstore _ | Craise -> false
        (* The remaining operations are simple if their args are *)
      | _ ->
          List.for_all self#is_simple_expr args
      end
  | _ -> false

(* Says whether an integer constant is a suitable immediate argument *)

method virtual is_immediate : int -> bool

(* Selection of addressing modes *)

method virtual select_addressing :
  Cmm.expression -> Arch.addressing_mode * Cmm.expression

(* Default instruction selection for stores (of words) *)

method select_store addr arg =
  (Istore(Word, addr), arg)

(* Default instruction selection for operators *)

method select_operation op args =
  match (op, args) with
    (Capply ty, {exp=Cconst_symbol s} :: rem) -> (Icall_imm s, rem)
  | (Capply ty, _) -> (Icall_ind, args)
  | (Cextcall(s, ty, alloc), _) -> (Iextcall(s, alloc), args)
  | (Cload chunk, [arg]) ->
      let (addr, eloc) = self#select_addressing arg in
      (Iload(chunk, addr), [eloc])
  | (Cstore chunk, [arg1; arg2]) ->
      let (addr, eloc) = self#select_addressing arg1 in
      if chunk = Word then begin
        let (op, newarg2) = self#select_store addr arg2 in
        (op, [newarg2; eloc])
      end else begin
        (Istore(chunk, addr), [arg2; eloc])
        (* Inversion addr/datum in Istore *)
      end
  | (Calloc, _) -> (Ialloc 0, args)
  | (Caddi, _) -> self#select_arith_comm Iadd args
  | (Csubi, _) -> self#select_arith Isub args
  | (Cmuli, [arg1; {exp=Cconst_int n}]) ->
      let l = Misc.log2 n in
      if n = 1 lsl l
      then (Iintop_imm(Ilsl, l), [arg1])
      else self#select_arith_comm Imul args
  | (Cmuli, [{exp=Cconst_int n}; arg1]) ->
      let l = Misc.log2 n in
      if n = 1 lsl l
      then (Iintop_imm(Ilsl, l), [arg1])
      else self#select_arith_comm Imul args
  | (Cmuli, _) -> self#select_arith_comm Imul args
  | (Cdivi, _) -> self#select_arith Idiv args
  | (Cmodi, _) -> self#select_arith_comm Imod args
  | (Cand, _) -> self#select_arith_comm Iand args
  | (Cor, _) -> self#select_arith_comm Ior args
  | (Cxor, _) -> self#select_arith_comm Ixor args
  | (Clsl, _) -> self#select_shift Ilsl args
  | (Clsr, _) -> self#select_shift Ilsr args
  | (Casr, _) -> self#select_shift Iasr args
  | (Ccmpi comp, _) -> self#select_arith_comp (Isigned comp) args
  | (Cadda, _) -> self#select_arith_comm Iadd args
  | (Csuba, _) -> self#select_arith Isub args
  | (Ccmpa comp, _) -> self#select_arith_comp (Iunsigned comp) args
  | (Cnegf, _) -> (Inegf, args)
  | (Cabsf, _) -> (Iabsf, args)
  | (Caddf, _) -> (Iaddf, args)
  | (Csubf, _) -> (Isubf, args)
  | (Cmulf, _) -> (Imulf, args)
  | (Cdivf, _) -> (Idivf, args)
  | (Cfloatofint, _) -> (Ifloatofint, args)
  | (Cintoffloat, _) -> (Iintoffloat, args)
  | (Ccheckbound, _) -> self#select_arith Icheckbound args
  | _ -> fatal_error "Selection.select_oper"

method private select_arith_comm op = function
    [arg; {exp=Cconst_int n}] when self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [arg; {exp=Cconst_pointer n}] when self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [{exp=Cconst_int n}; arg] when self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [{exp=Cconst_pointer n}; arg] when self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | args ->
      (Iintop op, args)

method private select_arith op = function
    [arg; {exp=Cconst_int n}] when self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | [arg; {exp=Cconst_pointer n}] when self#is_immediate n ->
      (Iintop_imm(op, n), [arg])
  | args ->
      (Iintop op, args)

method private select_shift op = function
    [arg; {exp=Cconst_int n}] when n >= 0 && n < Arch.size_int * 8 ->
      (Iintop_imm(op, n), [arg])
  | args ->
      (Iintop op, args)

method private select_arith_comp cmp = function
    [arg; {exp=Cconst_int n}] when self#is_immediate n ->
      (Iintop_imm(Icomp cmp, n), [arg])
  | [arg; {exp=Cconst_pointer n}] when self#is_immediate n ->
      (Iintop_imm(Icomp cmp, n), [arg])
  | [{exp=Cconst_int n}; arg] when self#is_immediate n ->
      (Iintop_imm(Icomp(swap_intcomp cmp), n), [arg])
  | [{exp=Cconst_pointer n}; arg] when self#is_immediate n ->
      (Iintop_imm(Icomp(swap_intcomp cmp), n), [arg])
  | args ->
      (Iintop(Icomp cmp), args)

(* Instruction selection for conditionals *)

method select_condition c =
  let mk = mkdbg c.dbg in
  match c.exp with
    Cop(Ccmpi cmp, [arg1; {exp=Cconst_int n}]) when self#is_immediate n ->
      (Iinttest_imm(Isigned cmp, n), arg1)
  | Cop(Ccmpi cmp, [{exp=Cconst_int n}; arg2]) when self#is_immediate n ->
      (Iinttest_imm(Isigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpi cmp, [arg1; {exp=Cconst_pointer n}]) when self#is_immediate n ->
      (Iinttest_imm(Isigned cmp, n), arg1)
  | Cop(Ccmpi cmp, [{exp=Cconst_pointer n}; arg2]) when self#is_immediate n ->
      (Iinttest_imm(Isigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpi cmp, args) ->
      (Iinttest(Isigned cmp), mk(Ctuple args))
  | Cop(Ccmpa cmp, [arg1; {exp=Cconst_pointer n}]) when self#is_immediate n ->
      (Iinttest_imm(Iunsigned cmp, n), arg1)
  | Cop(Ccmpa cmp, [arg1; {exp=Cconst_int n}]) when self#is_immediate n ->
      (Iinttest_imm(Iunsigned cmp, n), arg1)
  | Cop(Ccmpa cmp, [{exp=Cconst_pointer n}; arg2]) when self#is_immediate n ->
      (Iinttest_imm(Iunsigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpa cmp, [{exp=Cconst_int n}; arg2]) when self#is_immediate n ->
      (Iinttest_imm(Iunsigned(swap_comparison cmp), n), arg2)
  | Cop(Ccmpa cmp, args) ->
      (Iinttest(Iunsigned cmp), mk(Ctuple args))
  | Cop(Ccmpf cmp, args) ->
      (Ifloattest(cmp, false), mk(Ctuple args))
  | Cop(Cand, [arg; {exp=Cconst_int 1}]) ->
      (Ioddtest, arg)
  | _ ->
      (Itruetest, c)

(* Return an array of fresh registers of the given type.
   Normally implemented as Reg.createv, but some
   ports (e.g. Arm) can override this definition to store float values
   in pairs of integer registers. *)

method regs_for tys = Reg.createv tys

(* Buffering of instruction sequences *)

val mutable instr_seq = dummy_instr

method insert_debug desc dbg arg res =
  instr_seq <- instr_cons_debug desc arg res dbg instr_seq

method extract =
  let rec extract res i =
    if i == dummy_instr
    then res
    else extract {i with next = res} i.next in
  extract (end_instr()) instr_seq

(* Insert a sequence of moves from one pseudoreg set to another. *)

method insert_move dbg src dst =
  if src.stamp <> dst.stamp then
    self#insert_debug (Iop Imove) dbg [|src|] [|dst|]

method insert_moves dbg src dst =
  for i = 0 to Array.length src - 1 do
    self#insert_move dbg src.(i) dst.(i)
  done

(* Insert moves and stack offsets for function arguments and results *)

method insert_move_args dbg arg loc stacksize =
  if stacksize <> 0 then self#insert_debug (Iop(Istackoffset stacksize)) dbg [||] [||];
  self#insert_moves dbg arg loc

method insert_move_results dbg loc res stacksize =
  if stacksize <> 0 then self#insert_debug (Iop(Istackoffset(-stacksize))) dbg [||] [||];
  self#insert_moves dbg loc res

(* Add an Iop opcode. Can be overridden by processor description
   to insert moves before and after the operation, i.e. for two-address
   instructions, or instructions using dedicated registers. *)

method insert_op_debug op dbg rs rd =
  self#insert_debug (Iop op) dbg rs rd;
  rd

(*method insert_op op rs rd =
  self#insert (Iop op) rs rd;
  rd
*)
(* Add the instructions for the given expression
   at the end of the self sequence *)

method emit_expr env exp =
  let dbg = exp.dbg in
  let mk = mkdbg exp.dbg in
  match exp.exp with
    Cconst_int n ->
      let r = self#regs_for typ_int in
      Some(self#insert_op_debug (Iconst_int(Nativeint.of_int n)) dbg [||] r)
  | Cconst_natint n ->
      let r = self#regs_for typ_int in
      Some(self#insert_op_debug (Iconst_int n) dbg [||] r)
  | Cconst_float n ->
      let r = self#regs_for typ_float in
      Some(self#insert_op_debug (Iconst_float n) dbg [||] r)
  | Cconst_symbol n ->
      let r = self#regs_for typ_addr in
      Some(self#insert_op_debug (Iconst_symbol n) dbg [||] r)
  | Cconst_pointer n ->
      let r = self#regs_for typ_addr in
      Some(self#insert_op_debug (Iconst_int(Nativeint.of_int n)) dbg [||] r)
  | Cconst_natpointer n ->
      let r = self#regs_for typ_addr in
      Some(self#insert_op_debug (Iconst_int n) dbg [||] r)
  | Cvar v ->
      begin try
        Some(Tbl.find v env)
      with Not_found ->
        fatal_error("Selection.emit_expr: unbound var " ^ Ident.unique_name v)
      end
  | Clet(v, e1, e2) ->
      begin match self#emit_expr env e1 with
        None -> None
      | Some r1 -> self#emit_expr (self#bind_let env v r1) e2
      end
  | Cassign(v, e1) ->
      let rv =
        try
          Tbl.find v env
        with Not_found ->
          fatal_error ("Selection.emit_expr: unbound var " ^ Ident.name v) in
      begin match self#emit_expr env e1 with
        None -> None
      | Some r1 -> self#insert_moves dbg r1 rv; Some [||]
      end
  | Ctuple [] ->
      Some [||]
  | Ctuple exp_list ->
      begin match self#emit_parts_list env exp_list with
        None -> None
      | Some(simple_list, ext_env) ->
          Some(self#emit_tuple ext_env simple_list)
      end
  | Cop(Craise, [arg]) ->
      begin match self#emit_expr env arg with
        None -> None
      | Some r1 ->
          let rd = [|Proc.loc_exn_bucket|] in
          self#insert_debug (Iop Imove) dbg r1 rd;
          self#insert_debug Iraise dbg rd [||];
          None
      end
  | Cop(Ccmpf comp, args) ->
      self#emit_expr env (mk(Cifthenelse(exp, mk(Cconst_int 1), mk(Cconst_int 0))))
  | Cop(op, args) ->
      begin match self#emit_parts_list env args with
        None -> None
      | Some(simple_args, env) ->
          let ty = oper_result_type op in
          let (new_op, new_args) = self#select_operation op simple_args in
          match new_op with
            Icall_ind ->
              Proc.contains_calls := true;
              let r1 = self#emit_tuple env new_args in
              let rarg = Array.sub r1 1 (Array.length r1 - 1) in
              let rd = self#regs_for ty in
              let (loc_arg, stack_ofs) = Proc.loc_arguments rarg in
              let loc_res = Proc.loc_results rd in
              self#insert_move_args dbg rarg loc_arg stack_ofs;
              self#insert_debug (Iop Icall_ind) dbg
                          (Array.append [|r1.(0)|] loc_arg) loc_res;
              self#insert_move_results dbg loc_res rd stack_ofs;
              Some rd
          | Icall_imm lbl ->
              Proc.contains_calls := true;
              let r1 = self#emit_tuple env new_args in
              let rd = self#regs_for ty in
              let (loc_arg, stack_ofs) = Proc.loc_arguments r1 in
              let loc_res = Proc.loc_results rd in
              self#insert_move_args dbg r1 loc_arg stack_ofs;
              self#insert_debug (Iop(Icall_imm lbl)) dbg loc_arg loc_res;
              self#insert_move_results dbg loc_res rd stack_ofs;
              Some rd
          | Iextcall(lbl, alloc) ->
              Proc.contains_calls := true;
              let (loc_arg, stack_ofs) =
                self#emit_extcall_args env new_args in
              let rd = self#regs_for ty in
              let loc_res = Proc.loc_external_results rd in
              self#insert_debug (Iop(Iextcall(lbl, alloc))) dbg
                             loc_arg loc_res;
              self#insert_move_results dbg loc_res rd stack_ofs;
              Some rd
          | Ialloc _ ->
              Proc.contains_calls := true;
              let rd = self#regs_for typ_addr in
              let size = size_expr env (mk(Ctuple new_args)) in
              self#insert_debug (Iop(Ialloc size)) dbg [||] rd;
              self#emit_stores env new_args rd;
              Some rd
          | op ->
              let r1 = self#emit_tuple env new_args in
              let rd = self#regs_for ty in
              Some (self#insert_op_debug op dbg r1 rd)
      end
  | Csequence(e1, e2) ->
      begin match self#emit_expr env e1 with
        None -> None
      | Some r1 -> self#emit_expr env e2
      end
  | Cifthenelse(econd, eif, eelse) ->
      let (cond, earg) = self#select_condition econd in
      begin match self#emit_expr env earg with
        None -> None
      | Some rarg ->
          let (rif, sif) = self#emit_sequence env eif in
          let (relse, selse) = self#emit_sequence env eelse in
          let r = join rif sif relse selse in
          self#insert_debug (Iifthenelse(cond, sif#extract, selse#extract))
                      dbg rarg [||];
          r
      end
  | Cswitch(esel, index, ecases) ->
      begin match self#emit_expr env esel with
        None -> None
      | Some rsel ->
          let rscases = Array.map (self#emit_sequence env) ecases in
          let r = join_array rscases in
          self#insert_debug (Iswitch(index,
                               Array.map (fun (r, s) -> s#extract) rscases))
                      dbg rsel [||];
          r
      end
  | Cloop(ebody) ->
      let (rarg, sbody) = self#emit_sequence env ebody in
      self#insert_debug (Iloop(sbody#extract)) dbg [||] [||];
      Some [||]
  | Ccatch(nfail, ids, e1, e2) ->
      let rs =
        List.map
          (fun id ->
            let r = self#regs_for typ_addr in name_regs id r; r)
          ids in
      catch_regs := (nfail, Array.concat rs) :: !catch_regs ;
      let (r1, s1) = self#emit_sequence env e1 in
      catch_regs := List.tl !catch_regs ;
      let new_env =
        List.fold_left
        (fun env (id,r) -> Tbl.add id r env)
        env (List.combine ids rs) in
      let (r2, s2) = self#emit_sequence new_env e2 in
      let r = join r1 s1 r2 s2 in
      self#insert_debug (Icatch(nfail, s1#extract, s2#extract)) dbg [||] [||];
      r
  | Cexit (nfail,args) ->
      begin match self#emit_parts_list env args with
        None -> None
      | Some (simple_list, ext_env) ->
          let src = self#emit_tuple ext_env simple_list in
          let dest =
            try List.assoc nfail !catch_regs
            with Not_found ->
              Misc.fatal_error
                ("Selectgen.emit_expr, on exit("^string_of_int nfail^")") in
          self#insert_moves dbg src dest ;
          self#insert_debug (Iexit nfail) dbg [||] [||];
          None
      end
  | Ctrywith(e1, v, e2) ->
      Proc.contains_calls := true;
      let (r1, s1) = self#emit_sequence env e1 in
      let rv = self#regs_for typ_addr in
      let (r2, s2) = self#emit_sequence (Tbl.add v rv env) e2 in
      let r = join r1 s1 r2 s2 in
      self#insert_debug
        (Itrywith(s1#extract,
                  instr_cons_debug (Iop Imove) [|Proc.loc_exn_bucket|] rv
                             dbg (s2#extract)))
        dbg [||] [||];
      r
    
method private emit_sequence env exp =
  let s = {< instr_seq = dummy_instr >} in
  let r = s#emit_expr env exp in
  (r, s)

method private bind_let env v r1 =
  if all_regs_anonymous r1 then begin
    name_regs v r1;
    Tbl.add v r1 env
  end else begin
    let rv = Reg.createv_like r1 in
    name_regs v rv;
    self#insert_moves Debuginfo.none r1 rv;
    Tbl.add v rv env
  end

method private emit_parts env exp =
  let mk = mkdbg exp.dbg in
  if self#is_simple_expr exp then
    Some (exp, env)
  else begin
    match self#emit_expr env exp with
      None -> None
    | Some r ->
        if Array.length r = 0 then
          Some (mk(Ctuple []), env)
        else begin
          (* The normal case *)
          let id = Ident.create "bind" in
          if all_regs_anonymous r then
            (* r is an anonymous, unshared register; use it directly *)
            Some (mk(Cvar id), Tbl.add id r env)
          else begin
            (* Introduce a fresh temp to hold the result *)
            let tmp = Reg.createv_like r in
            self#insert_moves exp.dbg r tmp;
            Some (mk(Cvar id), Tbl.add id tmp env)
          end
        end
  end

method private emit_parts_list env exp_list =
  match exp_list with
    [] -> Some ([], env)
  | exp :: rem ->
      (* This ensures right-to-left evaluation, consistent with the
         bytecode compiler *)
      match self#emit_parts_list env rem with
        None -> None
      | Some(new_rem, new_env) ->
          match self#emit_parts new_env exp with
            None -> None
          | Some(new_exp, fin_env) -> Some(new_exp :: new_rem, fin_env)

method private emit_tuple env exp_list =
  let rec emit_list = function
    [] -> []
  | exp :: rem ->
      (* Again, force right-to-left evaluation *)
      let loc_rem = emit_list rem in
      match self#emit_expr env exp with
        None -> assert false  (* should have been caught in emit_parts *)
      | Some loc_exp -> loc_exp :: loc_rem in
  Array.concat(emit_list exp_list)

method emit_extcall_args env args =
  let r1 = self#emit_tuple env args in
  let (loc_arg, stack_ofs as arg_stack) = Proc.loc_external_arguments r1 in
  let dbg = Debuginfo.none in
  self#insert_move_args dbg r1 loc_arg stack_ofs;
  arg_stack

method emit_stores env data regs_addr =
  let a =
    ref (Arch.offset_addressing Arch.identity_addressing (-Arch.size_int)) in
  List.iter
    (fun e ->
      let (op, arg) = self#select_store !a e in
      match self#emit_expr env arg with
        None -> assert false
      | Some regs ->
          let dbg = arg.dbg in
          match op with
            Istore(_, _) ->
              for i = 0 to Array.length regs - 1 do
                let r = regs.(i) in
                let kind = if r.typ = Float then Double_u else Word in
                self#insert_debug (Iop(Istore(kind, !a))) dbg
                            (Array.append [|r|] regs_addr) [||];
                a := Arch.offset_addressing !a (size_component r.typ)
              done
          | _ ->
              self#insert_debug (Iop op) dbg (Array.append regs regs_addr) [||];
              a := Arch.offset_addressing !a (size_expr env e))
    data

(* Same, but in tail position *)

method private emit_return env exp =
  match self#emit_expr env exp with
    None -> ()
  | Some r ->
      let loc = Proc.loc_results r in
      let dbg = exp.dbg in
      self#insert_moves dbg r loc;
      self#insert_debug Ireturn dbg loc [||]

method emit_tail env exp =
  let dbg = exp.dbg in
  match exp.exp with
    Clet(v, e1, e2) ->
      begin match self#emit_expr env e1 with
        None -> ()
      | Some r1 -> self#emit_tail (self#bind_let env v r1) e2
      end
  | Cop(Capply ty as op, args) ->
      begin match self#emit_parts_list env args with
        None -> ()
      | Some(simple_args, env) ->
          let (new_op, new_args) = self#select_operation op simple_args in
          match new_op with
            Icall_ind ->
              let r1 = self#emit_tuple env new_args in
              let rarg = Array.sub r1 1 (Array.length r1 - 1) in
              let (loc_arg, stack_ofs) = Proc.loc_arguments rarg in
              if stack_ofs = 0 then begin
                self#insert_moves dbg rarg loc_arg;
                self#insert_debug (Iop Itailcall_ind) dbg
                            (Array.append [|r1.(0)|] loc_arg) [||]
              end else begin
                Proc.contains_calls := true;
                let rd = self#regs_for ty in
                let loc_res = Proc.loc_results rd in
                self#insert_move_args dbg rarg loc_arg stack_ofs;
                self#insert_debug (Iop Icall_ind) dbg
                            (Array.append [|r1.(0)|] loc_arg) loc_res;
                self#insert_debug (Iop(Istackoffset(-stack_ofs))) dbg [||] [||];
                self#insert_debug Ireturn dbg loc_res [||]
              end
          | Icall_imm lbl ->
              let r1 = self#emit_tuple env new_args in
              let (loc_arg, stack_ofs) = Proc.loc_arguments r1 in
              if stack_ofs = 0 then begin
                self#insert_moves dbg r1 loc_arg;
                self#insert_debug (Iop(Itailcall_imm lbl)) dbg loc_arg [||]
              end else if lbl = !current_function_name then begin
                let loc_arg' = Proc.loc_parameters r1 in
                self#insert_moves dbg r1 loc_arg';
                self#insert_debug (Iop(Itailcall_imm lbl)) dbg loc_arg' [||]
              end else begin
                Proc.contains_calls := true;
                let rd = self#regs_for ty in
                let loc_res = Proc.loc_results rd in
                self#insert_move_args dbg r1 loc_arg stack_ofs;
                self#insert_debug (Iop(Icall_imm lbl)) dbg loc_arg loc_res;
                self#insert_debug (Iop(Istackoffset(-stack_ofs))) dbg [||] [||];
                self#insert_debug Ireturn dbg loc_res [||]
              end
          | _ -> fatal_error "Selection.emit_tail"
      end
  | Csequence(e1, e2) ->
      begin match self#emit_expr env e1 with
        None -> ()
      | Some r1 -> self#emit_tail env e2
      end
  | Cifthenelse(econd, eif, eelse) ->
      let (cond, earg) = self#select_condition econd in
      begin match self#emit_expr env earg with
        None -> ()
      | Some rarg ->
          self#insert_debug (Iifthenelse(cond, self#emit_tail_sequence env eif,
                                         self#emit_tail_sequence env eelse))
                      dbg rarg [||]
      end
  | Cswitch(esel, index, ecases) ->
      begin match self#emit_expr env esel with
        None -> ()
      | Some rsel ->
          self#insert_debug
            (Iswitch(index, Array.map (self#emit_tail_sequence env) ecases))
            dbg rsel [||]
      end
  | Ccatch(nfail, ids, e1, e2) ->
       let rs =
        List.map
          (fun id ->
            let r = self#regs_for typ_addr in
            name_regs id r  ;
            r)
          ids in
      catch_regs := (nfail, Array.concat rs) :: !catch_regs ;
      let s1 = self#emit_tail_sequence env e1 in
      catch_regs := List.tl !catch_regs ;
      let new_env =
        List.fold_left
        (fun env (id,r) -> Tbl.add id r env)
        env (List.combine ids rs) in
      let s2 = self#emit_tail_sequence new_env e2 in
      self#insert_debug (Icatch(nfail, s1, s2)) dbg [||] [||]
  | Ctrywith(e1, v, e2) ->
      Proc.contains_calls := true;
      let (opt_r1, s1) = self#emit_sequence env e1 in
      let rv = self#regs_for typ_addr in
      let s2 = self#emit_tail_sequence (Tbl.add v rv env) e2 in
      self#insert_debug
        (Itrywith(s1#extract,
                  instr_cons_debug (Iop Imove) [|Proc.loc_exn_bucket|] rv dbg s2))
        dbg [||] [||];
      begin match opt_r1 with
        None -> ()
      | Some r1 ->
          let loc = Proc.loc_results r1 in
          self#insert_moves dbg r1 loc;
          self#insert_debug Ireturn dbg loc [||]
      end
  | _ ->
      self#emit_return env exp

method private emit_tail_sequence env exp =
  let s = {< instr_seq = dummy_instr >} in
  s#emit_tail env exp;
  s#extract

(* Sequentialization of a function definition *)

method emit_fundecl f =
  Proc.contains_calls := false;
  current_function_name := f.Cmm.fun_name;
  let rargs =
    List.map
      (fun (id, ty) -> let r = self#regs_for ty in name_regs id r; r)
      f.Cmm.fun_args in
  let rarg = Array.concat rargs in
  let loc_arg = Proc.loc_parameters rarg in
  let env =
    List.fold_right2
      (fun (id, ty) r env -> Tbl.add id r env)
      f.Cmm.fun_args rargs Tbl.empty in
  self#insert_moves Debuginfo.none loc_arg rarg;
  self#emit_tail env f.Cmm.fun_body;
  { fun_name = f.Cmm.fun_name;
    fun_args = loc_arg;
    fun_body = self#extract;
    fun_fast = f.Cmm.fun_fast }

end
