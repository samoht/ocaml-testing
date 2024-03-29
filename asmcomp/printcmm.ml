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

(* Pretty-printing of C-- code *)

open Format
open Cmm
open Debuginfo

let machtype_component ppf = function
  | Addr -> fprintf ppf "addr"
  | Int -> fprintf ppf "int"
  | Float -> fprintf ppf "float"

let machtype ppf mty =
  match Array.length mty with
  | 0 -> fprintf ppf "unit"
  | n -> machtype_component ppf mty.(0);
         for i = 1 to n-1 do
           fprintf ppf "*%a" machtype_component mty.(i)
         done

let comparison = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let chunk = function
  | Byte_unsigned -> "unsigned int8"
  | Byte_signed -> "signed int8"
  | Sixteen_unsigned -> "unsigned int16"
  | Sixteen_signed -> "signed int16"
  | Thirtytwo_unsigned -> "unsigned int32"
  | Thirtytwo_signed -> "signed int32"
  | Word -> ""
  | Single -> "float32"
  | Double -> "float64"
  | Double_u -> "float64u"

let operation = function
  | Capply(ty) -> "app"
  | Cextcall(lbl, ty, alloc) ->
      Printf.sprintf "extcall \"%s\"" lbl
  | Cload Word -> "load"
  | Cload c -> Printf.sprintf "load %s" (chunk c)
  | Calloc -> "alloc"
  | Cstore Word -> "store"
  | Cstore c -> Printf.sprintf "store %s" (chunk c)
  | Caddi -> "+"
  | Csubi -> "-"
  | Cmuli -> "*"
  | Cdivi -> "/"
  | Cmodi -> "mod"
  | Cand -> "and"
  | Cor -> "or"
  | Cxor -> "xor"
  | Clsl -> "<<"
  | Clsr -> ">>u"
  | Casr -> ">>s"
  | Ccmpi c -> comparison c
  | Cadda -> "+a"
  | Csuba -> "-a"
  | Ccmpa c -> Printf.sprintf "%sa" (comparison c)
  | Cnegf -> "~f"
  | Cabsf -> "absf"
  | Caddf -> "+f"
  | Csubf -> "-f"
  | Cmulf -> "*f"
  | Cdivf -> "/f"
  | Cfloatofint -> "floatofint"
  | Cintoffloat -> "intoffloat"
  | Ccmpf c -> Printf.sprintf "%sf" (comparison c)
  | Craise -> "raise"
  | Ccheckbound -> "checkbound"

let rec expr_desc ppf = function
  | Cconst_int n -> fprintf ppf "%i" n
  | Cconst_natint n -> fprintf ppf "%s" (Nativeint.to_string n)
  | Cconst_float s -> fprintf ppf "%s" s
  | Cconst_symbol s -> fprintf ppf "\"%s\"" s
  | Cconst_pointer n -> fprintf ppf "%ia" n
  | Cconst_natpointer n -> fprintf ppf "%sa" (Nativeint.to_string n)
  | Cvar id -> Ident.print ppf id
  | Clet(id, def, ({exp=Clet(_, _, _)} as body)) ->
      let print_binding id ppf def =
        fprintf ppf "@[<2>%a@ %a@]" Ident.print id expression def in
      let rec in_part ppf cmm = match cmm.exp with
        | Clet(id, def, body) ->
            fprintf ppf "@ %a" (print_binding id) def;
            in_part ppf body
        | _ -> cmm in
      fprintf ppf "@[<2>(let@ @[<1>(%a" (print_binding id) def;
      let exp = in_part ppf body in
      fprintf ppf ")@]@ %a)@]" sequence exp
  | Clet(id, def, body) ->
     fprintf ppf
      "@[<2>(let@ @[<2>%a@ %a@]@ %a)@]"
      Ident.print id expression def sequence body
  | Cassign(id, exp) ->
      fprintf ppf "@[<2>(assign @[<2>%a@ %a@])@]" Ident.print id expression exp
  | Ctuple el ->
      let tuple ppf el =
       let first = ref true in
       List.iter
        (fun e ->
          if !first then first := false else fprintf ppf "@ ";
          expression ppf e)
        el in
      fprintf ppf "@[<1>[%a]@]" tuple el
  | Cop(op, el) ->
      fprintf ppf "@[<2>(%s" (operation op);
      List.iter (fun e -> fprintf ppf "@ %a" expression e) el;
      begin match op with
      | Capply mty -> fprintf ppf "@ %a" machtype mty
      | Cextcall(_, mty, _) -> fprintf ppf "@ %a" machtype mty
      | _ -> ()
      end;
      fprintf ppf ")@]"
  | Csequence(e1, e2) ->
      fprintf ppf "@[<2>(seq@ %a@ %a)@]" sequence e1 sequence e2
  | Cifthenelse(e1, e2, e3) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" expression e1 expression e2 expression e3
  | Cswitch(e1, index, cases) ->
      let print_case i ppf =
        for j = 0 to Array.length index - 1 do
          if index.(j) = i then fprintf ppf "case %i:" j
        done in
      let print_cases ppf =
       for i = 0 to Array.length cases - 1 do
        fprintf ppf "@ @[<2>%t@ %a@]" (print_case i) sequence cases.(i)
       done in
      fprintf ppf "@[<v 0>@[<2>(switch@ %a@ @]%t)@]" expression e1 print_cases
  | Cloop e ->
      fprintf ppf "@[<2>(loop@ %a)@]" sequence e
  | Ccatch(i, ids, e1, e2) ->
      fprintf ppf
        "@[<2>(catch@ %a@;<1 -2>with(%d%a)@ %a)@]"
        sequence e1 i
        (fun ppf ids ->
          List.iter
            (fun id -> fprintf ppf " %a" Ident.print id)
            ids) ids
        sequence e2
  | Cexit (i, el) ->
      fprintf ppf "@[<2>(exit %d" i ;
      List.iter (fun e -> fprintf ppf "@ %a" expression e) el;
      fprintf ppf ")@]"
  | Ctrywith(e1, id, e2) ->
      fprintf ppf "@[<2>(try@ %a@;<1 -2>with@ %a@ %a)@]"
             sequence e1 Ident.print id sequence e2

and sequence ppf cmm = match cmm.exp with
  | Csequence(e1, e2) -> fprintf ppf "%a@ %a" sequence e1 sequence e2
  | _ -> expression ppf cmm

and expression ppf e =
  if is_none e.dbg then
    fprintf ppf "%a" expr_desc e.exp
  else
    fprintf ppf "%s:%a" (string_of_dbg e.dbg) expr_desc e.exp

let fundecl ppf f =
  let print_cases ppf cases =
    let first = ref true in
    List.iter
     (fun (id, ty) ->
       if !first then first := false else fprintf ppf "@ ";
       fprintf ppf "%a: %a" Ident.print id machtype ty)
     cases in
  fprintf ppf "@[<1>(function %s@;<1 4>@[<1>(%a)@]@ @[%a@])@]@."
         f.fun_name print_cases f.fun_args sequence f.fun_body

let data_item ppf = function
  | Cdefine_symbol s -> fprintf ppf "\"%s\":" s
  | Cdefine_label l -> fprintf ppf "L%i:" l
  | Cglobal_symbol s -> fprintf ppf "global \"%s\"" s
  | Cint8 n -> fprintf ppf "byte %i" n
  | Cint16 n -> fprintf ppf "int16 %i" n
  | Cint32 n -> fprintf ppf "int32 %s" (Nativeint.to_string n)
  | Cint n -> fprintf ppf "int %s" (Nativeint.to_string n)
  | Csingle f -> fprintf ppf "single %s" f
  | Cdouble f -> fprintf ppf "double %s" f
  | Csymbol_address s -> fprintf ppf "addr \"%s\"" s
  | Clabel_address l -> fprintf ppf "addr L%i" l
  | Cstring s -> fprintf ppf "string \"%s\"" s
  | Cskip n -> fprintf ppf "skip %i" n
  | Calign n -> fprintf ppf "align %i" n

let data ppf dl =
  let items ppf = List.iter (fun d -> fprintf ppf "@ %a" data_item d) dl in
  fprintf ppf "@[<hv 1>(data%t)@]" items

let phrase ppf = function
  | Cfunction f -> fundecl ppf f
  | Cdata dl -> data ppf dl
