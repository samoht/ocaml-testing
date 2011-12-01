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

(* Translation from closed lambda to C-- *)

open Misc
open Arch
open Asttypes
open Primitive
open Types
open Lambda
open Clambda
open Cmm
open Cmx_format

(* Local binding of complex expressions *)

let bind name arg fn =
  match arg.cmm_desc with
    Cvar _ | Cconst_int _ | Cconst_natint _ | Cconst_symbol _
  | Cconst_pointer _ | Cconst_natpointer _ -> fn arg
  | _ -> let id = Ident.create name in
         let mk = mkexpr in
         mk (Clet(id, arg, fn (mk (Cvar id))))

let bind_nonvar name arg fn =
  match arg.cmm_desc with
    Cconst_int _ | Cconst_natint _ | Cconst_symbol _
  | Cconst_pointer _ | Cconst_natpointer _ -> fn arg
  | _ -> let id = Ident.create name in
         let mk = mkexpr in
         mk (Clet(id, arg, fn (mk (Cvar id))))

(* Block headers. Meaning of the tag field: see stdlib/obj.ml *)

let float_tag = Cconst_int Obj.double_tag
let floatarray_tag = Cconst_int Obj.double_array_tag

let block_header tag sz =
  Nativeint.add (Nativeint.shift_left (Nativeint.of_int sz) 10)
                (Nativeint.of_int tag)
let closure_header sz = block_header Obj.closure_tag sz
let infix_header ofs = block_header Obj.infix_tag ofs
let float_header = block_header Obj.double_tag (size_float / size_addr)
let floatarray_header len =
      block_header Obj.double_array_tag (len * size_float / size_addr)
let string_header len =
      block_header Obj.string_tag ((len + size_addr) / size_addr)
let boxedint32_header = block_header Obj.custom_tag 2
let boxedint64_header = block_header Obj.custom_tag (1 + 8 / size_addr)
let boxedintnat_header = block_header Obj.custom_tag 2

let alloc_block_header tag sz = Cconst_natint(block_header tag sz)
let alloc_float_header = Cconst_natint(float_header)
let alloc_floatarray_header len = Cconst_natint(floatarray_header len)
let alloc_closure_header sz = Cconst_natint(closure_header sz)
let alloc_infix_header ofs = Cconst_natint(infix_header ofs)
let alloc_boxedint32_header = Cconst_natint(boxedint32_header)
let alloc_boxedint64_header = Cconst_natint(boxedint64_header)
let alloc_boxedintnat_header = Cconst_natint(boxedintnat_header)

(* Integers *)

let max_repr_int = max_int asr 1
let min_repr_int = min_int asr 1

let int_const dbg n =
  let mk = mkexpr_dbg dbg in
  if n <= max_repr_int && n >= min_repr_int
  then mk (Cconst_int((n lsl 1) + 1))
  else mk (Cconst_natint
             (Nativeint.add (Nativeint.shift_left (Nativeint.of_int n) 1) 1n))

let add_const c n =
  if n = 0 then c else
    let mk = mkexpr_dbg c.cmm_dbg in
    mk (Cop(Caddi, [c; mk (Cconst_int n)]))

let incr_int c =
  let mk = mkexpr_dbg c.cmm_dbg in
  match c.cmm_desc with
    Cconst_int n when n < max_int -> mk (Cconst_int(n+1))
  | Cop(Caddi, [c; {cmm_desc=Cconst_int n}]) when n < max_int -> add_const c (n + 1)
  | _ -> add_const c 1

let decr_int c =
  let mk = mkexpr_dbg c.cmm_dbg in
  match c.cmm_desc with
    Cconst_int n when n > min_int -> mk (Cconst_int(n-1))
  | Cop(Caddi, [c; {cmm_desc=Cconst_int n}]) when n > min_int -> add_const c (n - 1)
  | _ -> add_const c (-1)

let add_int c1 c2 =
  let mk = mkexpr_dbg c1.cmm_dbg in
  match (c1.cmm_desc, c2.cmm_desc) with
    (Cop(Caddi, [c1; {cmm_desc=Cconst_int n1}]),
     Cop(Caddi, [c2; {cmm_desc=Cconst_int n2}])) when no_overflow_add n1 n2 ->
      add_const (mk (Cop(Caddi, [c1; c2]))) (n1 + n2)
  | (Cop(Caddi, [c1; {cmm_desc=Cconst_int n1}]), _) ->
      add_const (mk (Cop(Caddi, [c1; c2]))) n1
  | (_, Cop(Caddi, [c2; {cmm_desc=Cconst_int n2}])) ->
      add_const (mk (Cop(Caddi, [c1; c2]))) n2
  | (Cconst_int _, _) ->
      mk (Cop(Caddi, [c2; c1]))
  | (_, _) ->
      mk (Cop(Caddi, [c1; c2]))

let sub_int c1 c2 =
  let mk = mkexpr_dbg c1.cmm_dbg in
  match (c1.cmm_desc, c2.cmm_desc) with
    (Cop(Caddi, [c1; {cmm_desc=Cconst_int n1}]),
     Cop(Caddi, [c2; {cmm_desc=Cconst_int n2}])) when no_overflow_sub n1 n2 ->
      add_const (mk ((Cop(Csubi, [c1; c2])))) (n1 - n2)
  | (Cop(Caddi, [c1; {cmm_desc=Cconst_int n1}]), _) ->
      add_const (mk (Cop(Csubi, [c1; c2]))) n1
  | (_, Cop(Caddi, [c2; {cmm_desc=Cconst_int n2}])) when n2 <> min_int ->
      add_const (mk (Cop(Csubi, [c1; c2]))) (-n2)
  | (_, Cconst_int n) when n <> min_int ->
      add_const c1 (-n)
  | (_, _) ->
      mk (Cop(Csubi, [c1; c2]))

let mul_int c1 c2 =
  let mk = mkexpr_dbg c1.cmm_dbg in
  match (c1.cmm_desc, c2.cmm_desc) with
    (Cconst_int 0, _) -> c1
  | (Cconst_int 1, _) -> c2
  | (_, Cconst_int 0) -> c2
  | (_, Cconst_int 1) -> c1
  | (_, _) -> mk (Cop(Cmuli, [c1; c2]))

let tag_int c = match c.cmm_desc with
    Cconst_int n -> int_const c.cmm_dbg n
  | _ ->
    let mk = mkexpr_dbg c.cmm_dbg in
    mk (Cop(Caddi, [mk (Cop(Clsl, [c; mk (Cconst_int 1)])); mk (Cconst_int 1)]))

let force_tag_int c = match c.cmm_desc with
    Cconst_int n -> int_const c.cmm_dbg n
  | _ ->
    let mk = mkexpr_dbg c.cmm_dbg in
    mk (Cop(Cor, [mk (Cop(Clsl, [c; mk (Cconst_int 1)])); mk (Cconst_int 1)]))

let untag_int c =
  let mk = mkexpr_dbg c.cmm_dbg in
  match c.cmm_desc with
    Cconst_int n -> mk (Cconst_int(n asr 1))
  | Cop(Caddi, [{cmm_desc=Cop(Clsl, [c; {cmm_desc=Cconst_int 1}])}; {cmm_desc=Cconst_int 1}]) -> c
  | Cop(Cor, [{cmm_desc=Cop(Casr, [c; {cmm_desc=Cconst_int n}])}; {cmm_desc=Cconst_int 1}])
    when n > 0 && n < size_int * 8 ->
      mk (Cop(Casr, [c; mk (Cconst_int (n+1))]))
  | Cop(Cor, [{cmm_desc=Cop(Clsr, [c; {cmm_desc=Cconst_int n}])}; {cmm_desc=Cconst_int 1}])
    when n > 0 && n < size_int * 8 ->
      mk (Cop(Clsr, [c; mk (Cconst_int (n+1))]))
  | Cop(Cor, [c; {cmm_desc=Cconst_int 1}]) -> mk (Cop(Casr, [c; mk (Cconst_int 1)]))
  | _ -> mk (Cop(Casr, [c; mk (Cconst_int 1)]))

let lsl_int c1 c2 =
  let mk = mkexpr_dbg c1.cmm_dbg in
  match (c1.cmm_desc, c2.cmm_desc) with
    (Cop(Clsl, [c; {cmm_desc=Cconst_int n1}]), Cconst_int n2)
    when n1 > 0 && n2 > 0 && n1 + n2 < size_int * 8 ->
      mk (Cop(Clsl, [c; mk (Cconst_int (n1 + n2))]))
  | (_, _) ->
      mk (Cop(Clsl, [c1; c2]))

let ignore_low_bit_int c = match c.cmm_desc with
    Cop(Caddi, [({cmm_desc=Cop(Clsl, [_; {cmm_desc=Cconst_int 1}])} as c); {cmm_desc=Cconst_int 1}]) -> c
  | Cop(Cor, [c; {cmm_desc=Cconst_int 1}]) -> c
  | _ -> c

let is_nonzero_constant c = match c.cmm_desc with
    Cconst_int n -> n <> 0
  | Cconst_natint n -> n <> 0n
  | _ -> false

let safe_divmod op c1 c2 dbg =
  let mk = mkexpr_dbg dbg in
  if !Clflags.fast || is_nonzero_constant c2 then
    mk (Cop(op, [c1; c2]))
  else
    bind "divisor" c2 (fun c2 ->
      mk (Cifthenelse(c2,
                  mk (Cop(op, [c1; c2])),
                  mk (Cop(Craise,
                      [mk (Cconst_symbol "caml_bucket_Division_by_zero")])))))

(* Bool *)

let test_bool c = match c.cmm_desc with
    Cop(Caddi, [{cmm_desc=Cop(Clsl, [c; {cmm_desc=Cconst_int 1}])}; {cmm_desc=Cconst_int 1}]) -> c
  | Cop(Clsl, [c; {cmm_desc=Cconst_int 1}]) -> c
  | _ ->
    let mk = mkexpr_dbg c.cmm_dbg in
    mk (Cop(Ccmpi Cne, [c; mk (Cconst_int 1)]))

(* Float *)

let box_float c =
  let mk = mkexpr_dbg c.cmm_dbg in
  mk (Cop(Calloc, [mk alloc_float_header; c]))

let rec unbox_float c =
  let mk = mkexpr_dbg c.cmm_dbg in
  match c.cmm_desc with
    Cop(Calloc, [header; c]) -> c
  | Clet(id, exp, body) -> mk (Clet(id, exp, unbox_float body))
  | Cifthenelse(cond, e1, e2) ->
      mk (Cifthenelse(cond, unbox_float e1, unbox_float e2))
  | Csequence(e1, e2) -> mk (Csequence(e1, unbox_float e2))
  | Cswitch(e, tbl, el) -> mk (Cswitch(e, tbl, Array.map unbox_float el))
  | Ccatch(n, ids, e1, e2) -> mk (Ccatch(n, ids, unbox_float e1, unbox_float e2))
  | Ctrywith(e1, id, e2) -> mk (Ctrywith(unbox_float e1, id, unbox_float e2))
  | _ -> mk (Cop(Cload Double_u, [c]))

(* Complex *)

let box_complex c_re c_im =
  let mk = mkexpr_dbg c_re.cmm_dbg in
  mk (Cop(Calloc, [mk (alloc_floatarray_header 2); c_re; c_im]))

let complex_re c =
  let mk = mkexpr_dbg c.cmm_dbg in
  mk (Cop(Cload Double_u, [c]))

let complex_im c =
  let mk = mkexpr_dbg c.cmm_dbg in
  mk (Cop(Cload Double_u,
          [mk (Cop(Cadda, [c; mk (Cconst_int size_float)]))]))

(* Unit *)

let return_unit c =
  let mk = mkexpr_dbg c.cmm_dbg in
  mk (Csequence(c, mk (Cconst_pointer 1)))

let rec remove_unit c =
  let mk = mkexpr_dbg c.cmm_dbg in
  match c.cmm_desc with
    Cconst_pointer 1 -> mk (Ctuple [])
  | Csequence(c, {cmm_desc=Cconst_pointer 1}) -> c
  | Csequence(c1, c2) ->
      mk (Csequence(c1, remove_unit c2))
  | Cifthenelse(cond, ifso, ifnot) ->
      mk (Cifthenelse(cond, remove_unit ifso, remove_unit ifnot))
  | Cswitch(sel, index, cases) ->
      mk (Cswitch(sel, index, Array.map remove_unit cases))
  | Ccatch(io, ids, body, handler) ->
      mk (Ccatch(io, ids, remove_unit body, remove_unit handler))
  | Ctrywith(body, exn, handler) ->
      mk (Ctrywith(remove_unit body, exn, remove_unit handler))
  | Clet(id, c1, c2) ->
      mk (Clet(id, c1, remove_unit c2))
  | Cop(Capply mty, args) ->
      mk (Cop(Capply (typ_void), args))
  | Cop(Cextcall(proc, mty, alloc), args) ->
      mk (Cop(Cextcall(proc, typ_void, alloc), args))
  | Cexit (_,_) -> c
  | Ctuple [] -> c
  | _ -> mk (Csequence(c, mk (Ctuple [])))

(* Access to block fields *)

let field_address ptr n =
  if n = 0
  then ptr
  else
    let mk = mkexpr_dbg ptr.cmm_dbg in
    mk (Cop(Cadda, [ptr; mk (Cconst_int(n * size_addr))]))

let get_field ptr n =
  let mk = mkexpr_dbg ptr.cmm_dbg in
  mk (Cop(Cload Word, [field_address ptr n]))

let set_field ptr n newval =
  let mk = mkexpr_dbg ptr.cmm_dbg in
  mk (Cop(Cstore Word, [field_address ptr n; newval]))

let header ptr =
  let mk = mkexpr_dbg ptr.cmm_dbg in
  mk (Cop(Cload Word, [mk (Cop(Cadda, [ptr; mk (Cconst_int(-size_int))]))]))

let tag_offset =
  if big_endian then -1 else -size_int

let get_tag ptr =
  let mk = mkexpr_dbg ptr.cmm_dbg in
  if Proc.word_addressed then           (* If byte loads are slow *)
    mk (Cop(Cand, [header ptr; mk (Cconst_int 255)]))
  else                                  (* If byte loads are efficient *)
    mk (Cop(Cload Byte_unsigned,
        [mk (Cop(Cadda, [ptr; mk (Cconst_int(tag_offset))]))]))

let get_size ptr =
  let mk = mkexpr_dbg ptr.cmm_dbg in
  mk (Cop(Clsr, [header ptr; mk (Cconst_int 10)]))

(* Array indexing *)

let log2_size_addr = Misc.log2 size_addr
let log2_size_float = Misc.log2 size_float

let wordsize_shift = 9
let numfloat_shift = 9 + log2_size_float - log2_size_addr

let is_addr_array_hdr hdr =
  let mk = mkexpr_dbg hdr.cmm_dbg in
  mk (Cop(Ccmpi Cne, [mk (Cop(Cand, [hdr; mk (Cconst_int 255)])); mk floatarray_tag]))

let is_addr_array_ptr ptr =
  let mk = mkexpr_dbg ptr.cmm_dbg in
  mk (Cop(Ccmpi Cne, [get_tag ptr; mk floatarray_tag]))

let addr_array_length hdr =
  let mk = mkexpr_dbg hdr.cmm_dbg in
  mk (Cop(Clsr, [hdr; mk (Cconst_int wordsize_shift)]))

let float_array_length hdr =
  let mk = mkexpr_dbg hdr.cmm_dbg in
  mk (Cop(Clsr, [hdr; mk (Cconst_int numfloat_shift)]))

let lsl_const c n =
  let mk = mkexpr_dbg c.cmm_dbg in
  mk (Cop(Clsl, [c; mk (Cconst_int n)]))

let array_indexing log2size ptr ofs =
  let mk = mkexpr_dbg ptr.cmm_dbg in
  match ofs.cmm_desc with
    Cconst_int n ->
      let i = n asr 1 in
      if i = 0 then ptr else mk (Cop(Cadda, [ptr; mk (Cconst_int(i lsl log2size))]))
  | Cop(Caddi, [{cmm_desc=Cop(Clsl, [c; {cmm_desc=Cconst_int 1}])}; {cmm_desc=Cconst_int 1}]) ->
      mk (Cop(Cadda, [ptr; lsl_const c log2size]))
  | Cop(Caddi, [c; {cmm_desc=Cconst_int n}]) ->
      mk (Cop(Cadda, [mk(Cop(Cadda, [ptr; lsl_const c (log2size - 1)]));
                      mk (Cconst_int((n-1) lsl (log2size - 1)))]))
  | _ ->
      mk (Cop(Cadda, [mk (Cop(Cadda, [ptr; lsl_const ofs (log2size - 1)]));
                      mk (Cconst_int((-1) lsl (log2size - 1)))]))

let addr_array_ref arr ofs =
  let mk = mkexpr_dbg arr.cmm_dbg in
  mk (Cop(Cload Word, [array_indexing log2_size_addr arr ofs]))

let unboxed_float_array_ref arr ofs =
  let mk = mkexpr_dbg arr.cmm_dbg in
  mk (Cop(Cload Double_u, [array_indexing log2_size_float arr ofs]))

let float_array_ref arr ofs =
  box_float(unboxed_float_array_ref arr ofs)

let addr_array_set arr ofs newval =
  let mk = mkexpr_dbg arr.cmm_dbg in
  mk (Cop(Cextcall("caml_modify", typ_void, false),
          [array_indexing log2_size_addr arr ofs; newval]))

let int_array_set arr ofs newval =
  let mk = mkexpr_dbg arr.cmm_dbg in
  mk (Cop(Cstore Word, [array_indexing log2_size_addr arr ofs; newval]))

let float_array_set arr ofs newval =
  let mk = mkexpr_dbg arr.cmm_dbg in
  mk (Cop(Cstore Double_u, [array_indexing log2_size_float arr ofs; newval]))

(* String length *)

let string_length exp =
  bind "str" exp (fun str ->
    let tmp_var = Ident.create "tmp" in
    let mk = mkexpr_dbg exp.cmm_dbg in
    mk (Clet(tmp_var,
             mk (Cop(Csubi,
                     [mk (Cop(Clsl,
                              [mk (Cop(Clsr, [header str; mk (Cconst_int 10)]));
                               mk (Cconst_int log2_size_addr)]));
                      mk (Cconst_int 1)])),
             mk (Cop(Csubi,
                     [mk (Cvar tmp_var);
                      mk (Cop(Cload Byte_unsigned,
                              [mk (Cop(Cadda, [str; mk (Cvar tmp_var)]))]))])))))

(* Message sending *)

let lookup_tag obj tag =
  bind "tag" tag (fun tag ->
    let mk = mkexpr_dbg obj.cmm_dbg in
    mk (Cop(Cextcall("caml_get_public_method", typ_addr, false), [obj; tag])))

let lookup_label obj lab =
  bind "lab" lab (fun lab ->
    let mk = mkexpr_dbg obj.cmm_dbg in
    let table = mk (Cop (Cload Word, [obj])) in
    addr_array_ref table lab)

let call_cached_method obj tag cache pos args dbg =
  let arity = List.length args in
  let cache = array_indexing log2_size_addr cache pos in
  let mk = mkexpr_dbg obj.cmm_dbg in
  Compilenv.need_send_fun arity;
  mk (Cop(Capply (typ_addr),
          mk (Cconst_symbol("caml_send" ^ string_of_int arity)) ::
            obj :: tag :: cache :: args))

(* Allocation *)

let make_alloc_generic set_fn tag wordsize args dbg =
  let mk = mkexpr_dbg dbg in
  if wordsize <= Config.max_young_wosize then
    mk (Cop(Calloc, mk (Cconst_natint(block_header tag wordsize)) :: args))
  else begin
    let id = Ident.create "alloc" in
    let rec fill_fields idx = function
      | []     -> mk (Cvar id)
      | e1::el -> mk (Csequence(set_fn (mk (Cvar id)) (mk (Cconst_int idx)) e1,
                                fill_fields (idx + 2) el)) in
    mk (Clet(id,
             mk(Cop(Cextcall("caml_alloc", typ_addr, true),
                    [mk (Cconst_int wordsize); mk (Cconst_int tag)])),
             fill_fields 1 args))
  end

let make_alloc tag args dbg =
  make_alloc_generic addr_array_set tag (List.length args) args dbg
let make_float_alloc tag args dbg =
  make_alloc_generic float_array_set tag
                     (List.length args * size_float / size_addr) args dbg

(* To compile "let rec" over values *)

let fundecls_size fundecls =
  let sz = ref (-1) in
  List.iter
    (fun f -> sz := !sz + 1 + (if f.uf_arity = 1 then 2 else 3))
    fundecls;
  !sz

type rhs_kind =
  | RHS_block of int
  | RHS_nonrec
;;
let rec expr_size ulam = match ulam.ul_desc with
  | Uclosure(fundecls, clos_vars) ->
      RHS_block (fundecls_size fundecls + List.length clos_vars)
  | Ulet(id, exp, body) ->
      expr_size body
  | Uletrec(bindings, body) ->
      expr_size body
  | Uprim(Pmakeblock(tag, mut), args) ->
      RHS_block (List.length args)
  | Uprim(Pmakearray(Paddrarray | Pintarray), args) ->
      RHS_block (List.length args)
  | Usequence(exp, exp') ->
      expr_size exp'
  | _ -> RHS_nonrec

(* Record application and currying functions *)

let apply_function n =
  Compilenv.need_apply_fun n; "caml_apply" ^ string_of_int n
let curry_function n =
  Compilenv.need_curry_fun n;
  if n >= 0
  then "caml_curry" ^ string_of_int n
  else "caml_tuplify" ^ string_of_int (-n)

(* Comparisons *)

let transl_comparison = function
    Lambda.Ceq -> Ceq
  | Lambda.Cneq -> Cne
  | Lambda.Cge -> Cge
  | Lambda.Cgt -> Cgt
  | Lambda.Cle -> Cle
  | Lambda.Clt -> Clt

(* Translate structured constants *)

(* Fabrice: moved to compilenv.ml ----
let const_label = ref 0

let new_const_label () =
  incr const_label;
  !const_label

let new_const_symbol () =
  incr const_label;
  Compilenv.make_symbol (Some (string_of_int !const_label))

let structured_constants = ref ([] : (string * structured_constant) list)
*)

let transl_constant = function
    Const_base(Const_int n) ->
      int_const Debuginfo.none n
  | Const_base(Const_char c) ->
      mkexpr (Cconst_int (((Char.code c) lsl 1) + 1))
  | Const_pointer n ->
      if n <= max_repr_int && n >= min_repr_int
      then mkexpr (Cconst_pointer((n lsl 1) + 1))
      else mkexpr (Cconst_natpointer
                     (Nativeint.add (Nativeint.shift_left (Nativeint.of_int n) 1) 1n))
  | cst ->
    mkexpr (Cconst_symbol (Compilenv.new_structured_constant cst false))

(* Translate constant closures *)

let constant_closures =
  ref ([] : (string * Clambda.ufun list) list)

(* Boxed integers *)

let box_int_constant bi n =
  match bi with
    Pnativeint -> Const_base(Const_nativeint n)
  | Pint32 -> Const_base(Const_int32 (Nativeint.to_int32 n))
  | Pint64 -> Const_base(Const_int64 (Int64.of_nativeint n))

let operations_boxed_int bi =
  match bi with
    Pnativeint -> "caml_nativeint_ops"
  | Pint32 -> "caml_int32_ops"
  | Pint64 -> "caml_int64_ops"

let alloc_header_boxed_int bi =
  match bi with
    Pnativeint -> alloc_boxedintnat_header
  | Pint32 -> alloc_boxedint32_header
  | Pint64 -> alloc_boxedint64_header

let box_int bi arg =
  let mk = mkexpr_dbg arg.cmm_dbg in
  match arg.cmm_desc with
    Cconst_int n ->
      transl_constant (box_int_constant bi (Nativeint.of_int n))
  | Cconst_natint n ->
      transl_constant (box_int_constant bi n)
  | _ ->
      let arg' =
        if bi = Pint32 && size_int = 8 && big_endian
        then mk (Cop(Clsl, [arg; mk (Cconst_int 32)]))
        else arg in
      mk (Cop(Calloc, [mk (alloc_header_boxed_int bi);
                       mk (Cconst_symbol(operations_boxed_int bi));
                       arg']))

let rec unbox_int bi arg =
  let mk = mkexpr_dbg arg.cmm_dbg in
  match arg.cmm_desc with
    Cop(Calloc, [hdr; ops; {cmm_desc=Cop(Clsl, [contents; {cmm_desc=Cconst_int 32}])}])
    when bi = Pint32 && size_int = 8 && big_endian ->
      (* Force sign-extension of low 32 bits *)
      mk (Cop(Casr, [mk (Cop(Clsl, [contents; mk(Cconst_int 32)])); mk (Cconst_int 32)]))
  | Cop(Calloc, [hdr; ops; contents])
    when bi = Pint32 && size_int = 8 && not big_endian ->
      (* Force sign-extension of low 32 bits *)
      mk (Cop(Casr, [mk (Cop(Clsl, [contents; mk (Cconst_int 32)])); mk (Cconst_int 32)]))
  | Cop(Calloc, [hdr; ops; contents]) ->
      contents
  | Clet(id, exp, body) -> mk (Clet(id, exp, unbox_int bi body))
  | Cifthenelse(cond, e1, e2) ->
      mk (Cifthenelse(cond, unbox_int bi e1, unbox_int bi e2))
  | Csequence(e1, e2) -> mk (Csequence(e1, unbox_int bi e2))
  | Cswitch(e, tbl, el) -> mk (Cswitch(e, tbl, Array.map (unbox_int bi) el))
  | Ccatch(n, ids, e1, e2) -> mk (Ccatch(n, ids, unbox_int bi e1, unbox_int bi e2))
  | Ctrywith(e1, id, e2) -> mk (Ctrywith(unbox_int bi e1, id, unbox_int bi e2))
  | _ ->
      mk (Cop(Cload(if bi = Pint32 then Thirtytwo_signed else Word),
              [mk (Cop(Cadda, [arg; mk (Cconst_int size_addr)]))]))

let make_unsigned_int bi arg =
  let mk = mkexpr_dbg arg.cmm_dbg in  
  if bi = Pint32 && size_int = 8
  then mk (Cop(Cand, [arg; mk (Cconst_natint 0xFFFFFFFFn)]))
  else arg

(* Big arrays *)

let bigarray_elt_size = function
    Pbigarray_unknown -> assert false
  | Pbigarray_float32 -> 4
  | Pbigarray_float64 -> 8
  | Pbigarray_sint8 -> 1
  | Pbigarray_uint8 -> 1
  | Pbigarray_sint16 -> 2
  | Pbigarray_uint16 -> 2
  | Pbigarray_int32 -> 4
  | Pbigarray_int64 -> 8
  | Pbigarray_caml_int -> size_int
  | Pbigarray_native_int -> size_int
  | Pbigarray_complex32 -> 8
  | Pbigarray_complex64 -> 16

let bigarray_indexing unsafe elt_kind layout b args dbg =
  let mk = mkexpr_dbg dbg in
  let check_bound a1 a2 k =
    if unsafe then k else
      mk (Csequence(mk(Cop(Ccheckbound, [a1;a2])), k)) in
  let rec ba_indexing dim_ofs delta_ofs = function
    [] -> assert false
  | [arg] ->
      bind "idx" (untag_int arg)
        (fun idx ->
          check_bound (mk (Cop(Cload Word,[field_address b dim_ofs]))) idx idx)
  | arg1 :: argl ->
      let rem = ba_indexing (dim_ofs + delta_ofs) delta_ofs argl in
      bind "idx" (untag_int arg1)
        (fun idx ->
          bind "bound" (mk (Cop(Cload Word, [field_address b dim_ofs])))
          (fun bound ->
            check_bound bound idx (add_int (mul_int rem bound) idx))) in
  let offset =
    match layout with
      Pbigarray_unknown_layout ->
        assert false
    | Pbigarray_c_layout ->
        ba_indexing (4 + List.length args) (-1) (List.rev args)
    | Pbigarray_fortran_layout ->
        ba_indexing 5 1 (List.map (fun idx -> sub_int idx (mk(Cconst_int 2))) args)
  and elt_size =
    bigarray_elt_size elt_kind in
  let byte_offset =
    if elt_size = 1
    then offset
    else mk (Cop(Clsl, [offset; mk (Cconst_int(log2 elt_size))])) in
  mk (Cop(Cadda, [mk(Cop(Cload Word, [field_address b 1])); byte_offset]))

let bigarray_word_kind = function
    Pbigarray_unknown -> assert false
  | Pbigarray_float32 -> Single
  | Pbigarray_float64 -> Double
  | Pbigarray_sint8 -> Byte_signed
  | Pbigarray_uint8 -> Byte_unsigned
  | Pbigarray_sint16 -> Sixteen_signed
  | Pbigarray_uint16 -> Sixteen_unsigned
  | Pbigarray_int32 -> Thirtytwo_signed
  | Pbigarray_int64 -> Word
  | Pbigarray_caml_int -> Word
  | Pbigarray_native_int -> Word
  | Pbigarray_complex32 -> Single
  | Pbigarray_complex64 -> Double

let bigarray_get unsafe elt_kind layout b args dbg =
  let mk = mkexpr_dbg dbg in
  bind "ba" b (fun b ->
    match elt_kind with
      Pbigarray_complex32 | Pbigarray_complex64 ->
        let kind = bigarray_word_kind elt_kind in
        let sz = bigarray_elt_size elt_kind / 2 in
        bind "addr" (bigarray_indexing unsafe elt_kind layout b args dbg) (fun addr ->
          box_complex
            (mk(Cop(Cload kind, [addr])))
            (mk(Cop(Cload kind, [mk(Cop(Cadda, [addr; mk(Cconst_int sz)]))]))))
    | _ ->
        mk (Cop(Cload (bigarray_word_kind elt_kind),
                [bigarray_indexing unsafe elt_kind layout b args dbg])))

let bigarray_set unsafe elt_kind layout b args newval dbg =
  let mk = mkexpr_dbg dbg in
  bind "ba" b (fun b ->
    match elt_kind with
      Pbigarray_complex32 | Pbigarray_complex64 ->
        let kind = bigarray_word_kind elt_kind in
        let sz = bigarray_elt_size elt_kind / 2 in
        bind "newval" newval (fun newv ->
        bind "addr" (bigarray_indexing unsafe elt_kind layout b args dbg) (fun addr ->
          mk(Csequence(
            mk(Cop(Cstore kind, [addr; complex_re newv])),
            mk(Cop(Cstore kind,
                [mk(Cop(Cadda, [addr; mk(Cconst_int sz)])); complex_im newv]))))))
    | _ ->
        mk(Cop(Cstore (bigarray_word_kind elt_kind),
            [bigarray_indexing unsafe elt_kind layout b args dbg; newval])))

(* Simplification of some primitives into C calls *)

let default_prim name =
  { prim_name = name; prim_arity = 0 (*ignored*);
    prim_alloc = true; prim_native_name = ""; prim_native_float = false }

let simplif_primitive_32bits = function
    Pbintofint Pint64 -> Pccall (default_prim "caml_int64_of_int")
  | Pintofbint Pint64 -> Pccall (default_prim "caml_int64_to_int")
  | Pcvtbint(Pint32, Pint64) -> Pccall (default_prim "caml_int64_of_int32")
  | Pcvtbint(Pint64, Pint32) -> Pccall (default_prim "caml_int64_to_int32")
  | Pcvtbint(Pnativeint, Pint64) ->
      Pccall (default_prim "caml_int64_of_nativeint")
  | Pcvtbint(Pint64, Pnativeint) ->
      Pccall (default_prim "caml_int64_to_nativeint")
  | Pnegbint Pint64 -> Pccall (default_prim "caml_int64_neg")
  | Paddbint Pint64 -> Pccall (default_prim "caml_int64_add")
  | Psubbint Pint64 -> Pccall (default_prim "caml_int64_sub")
  | Pmulbint Pint64 -> Pccall (default_prim "caml_int64_mul")
  | Pdivbint Pint64 -> Pccall (default_prim "caml_int64_div")
  | Pmodbint Pint64 -> Pccall (default_prim "caml_int64_mod")
  | Pandbint Pint64 -> Pccall (default_prim "caml_int64_and")
  | Porbint Pint64 ->  Pccall (default_prim "caml_int64_or")
  | Pxorbint Pint64 -> Pccall (default_prim "caml_int64_xor")
  | Plslbint Pint64 -> Pccall (default_prim "caml_int64_shift_left")
  | Plsrbint Pint64 -> Pccall (default_prim "caml_int64_shift_right_unsigned")
  | Pasrbint Pint64 -> Pccall (default_prim "caml_int64_shift_right")
  | Pbintcomp(Pint64, Lambda.Ceq) -> Pccall (default_prim "caml_equal")
  | Pbintcomp(Pint64, Lambda.Cneq) -> Pccall (default_prim "caml_notequal")
  | Pbintcomp(Pint64, Lambda.Clt) -> Pccall (default_prim "caml_lessthan")
  | Pbintcomp(Pint64, Lambda.Cgt) -> Pccall (default_prim "caml_greaterthan")
  | Pbintcomp(Pint64, Lambda.Cle) -> Pccall (default_prim "caml_lessequal")
  | Pbintcomp(Pint64, Lambda.Cge) -> Pccall (default_prim "caml_greaterequal")
  | Pbigarrayref(unsafe, n, Pbigarray_int64, layout) ->
      Pccall (default_prim ("caml_ba_get_" ^ string_of_int n))
  | Pbigarrayset(unsafe, n, Pbigarray_int64, layout) ->
      Pccall (default_prim ("caml_ba_set_" ^ string_of_int n))
  | p -> p

let simplif_primitive p =
  match p with
  | Pduprecord _ ->
      Pccall (default_prim "caml_obj_dup")
  | Pbigarrayref(unsafe, n, Pbigarray_unknown, layout) ->
      Pccall (default_prim ("caml_ba_get_" ^ string_of_int n))
  | Pbigarrayset(unsafe, n, Pbigarray_unknown, layout) ->
      Pccall (default_prim ("caml_ba_set_" ^ string_of_int n))
  | Pbigarrayref(unsafe, n, kind, Pbigarray_unknown_layout) ->
      Pccall (default_prim ("caml_ba_get_" ^ string_of_int n))
  | Pbigarrayset(unsafe, n, kind, Pbigarray_unknown_layout) ->
      Pccall (default_prim ("caml_ba_set_" ^ string_of_int n))
  | p ->
      if size_int = 8 then p else simplif_primitive_32bits p

(* Build switchers both for constants and blocks *)

(* constants first *)

let transl_isout h arg =
  let mk = mkexpr_dbg arg.cmm_dbg in
  tag_int (mk(Cop(Ccmpa Clt, [h ; arg])))

exception Found of int

let make_switch_gen arg cases acts =
  let lcases = Array.length cases in
  let new_cases = Array.create lcases 0 in
  let store = Switch.mk_store (=) in

  for i = 0 to Array.length cases-1 do
    let act = cases.(i) in
    let new_act = store.Switch.act_store act in
    new_cases.(i) <- new_act
  done ;

  let mk = mkexpr_dbg arg.cmm_dbg in
  mk(Cswitch
    (arg, new_cases,
     Array.map
       (fun n -> acts.(n))
       (store.Switch.act_get ())))


(* Then for blocks *)

module SArgBlocks =
struct
  type primitive = operation

  let eqint = Ccmpi Ceq
  let neint = Ccmpi Cne
  let leint = Ccmpi Cle
  let ltint = Ccmpi Clt
  let geint = Ccmpi Cge
  let gtint = Ccmpi Cgt

  type act = expression

  let default = mkexpr(Cexit (0,[]))
  let make_prim p args = mkexpr(Cop (p,args))
  let make_offset arg n = add_const arg n
  let make_isout h arg =  mkexpr_dbg arg.cmm_dbg (Cop (Ccmpa Clt, [h ; arg]))
  let make_isin h arg =  mkexpr_dbg arg.cmm_dbg (Cop (Ccmpa Cge, [h ; arg]))
  let make_if cond ifso ifnot = mkexpr_dbg cond.cmm_dbg (Cifthenelse (cond, ifso, ifnot))
  let make_switch arg cases actions =
    make_switch_gen arg cases actions
  let bind arg body = bind "switcher" arg body

end

module SwitcherBlocks = Switch.Make(SArgBlocks)

(* Auxiliary functions for optimizing "let" of boxed numbers (floats and
   boxed integers *)

type unboxed_number_kind =
    No_unboxing
  | Boxed_float
  | Boxed_integer of boxed_integer

let is_unboxed_number ulam = match ulam.ul_desc with
    Uconst(Const_base(Const_float f), _) ->
      Boxed_float
  | Uprim(p, _) ->
      begin match simplif_primitive p with
          Pccall p -> if p.prim_native_float then Boxed_float else No_unboxing
        | Pfloatfield _ -> Boxed_float
        | Pfloatofint -> Boxed_float
        | Pnegfloat -> Boxed_float
        | Pabsfloat -> Boxed_float
        | Paddfloat -> Boxed_float
        | Psubfloat -> Boxed_float
        | Pmulfloat -> Boxed_float
        | Pdivfloat -> Boxed_float
        | Parrayrefu Pfloatarray -> Boxed_float
        | Parrayrefs Pfloatarray -> Boxed_float
        | Pbintofint bi -> Boxed_integer bi
        | Pcvtbint(src, dst) -> Boxed_integer dst
        | Pnegbint bi -> Boxed_integer bi
        | Paddbint bi -> Boxed_integer bi
        | Psubbint bi -> Boxed_integer bi
        | Pmulbint bi -> Boxed_integer bi
        | Pdivbint bi -> Boxed_integer bi
        | Pmodbint bi -> Boxed_integer bi
        | Pandbint bi -> Boxed_integer bi
        | Porbint bi -> Boxed_integer bi
        | Pxorbint bi -> Boxed_integer bi
        | Plslbint bi -> Boxed_integer bi
        | Plsrbint bi -> Boxed_integer bi
        | Pasrbint bi -> Boxed_integer bi
        | Pbigarrayref(_, _, (Pbigarray_float32 | Pbigarray_float64), _) ->
            Boxed_float
        | Pbigarrayref(_, _, Pbigarray_int32, _) -> Boxed_integer Pint32
        | Pbigarrayref(_, _, Pbigarray_int64, _) -> Boxed_integer Pint64
        | Pbigarrayref(_, _, Pbigarray_native_int, _) -> Boxed_integer Pnativeint
        | _ -> No_unboxing
      end
  | _ -> No_unboxing

let subst_boxed_number unbox_fn boxed_id unboxed_id exp =
  let need_boxed = ref false in
  let assigned = ref false in
  let rec subst c =
    let mk = mkexpr_dbg c.cmm_dbg in
    match c.cmm_desc with
      Cvar id ->
        if Ident.same id boxed_id then need_boxed := true; c
    | Clet(id, arg, body) -> mk(Clet(id, subst arg, subst body))
    | Cassign(id, arg) ->
        if Ident.same id boxed_id then begin
          assigned := true;
          mk(Cassign(unboxed_id, subst(unbox_fn arg)))
        end else
          mk(Cassign(id, subst arg))
    | Ctuple argv -> mk(Ctuple(List.map subst argv))
    | Cop(Cload _, [{cmm_desc=Cvar id}]) ->
        if Ident.same id boxed_id then mk(Cvar unboxed_id) else c
    | Cop(Cload _, [{cmm_desc=Cop(Cadda, [{cmm_desc=Cvar id}; _])}]) ->
        if Ident.same id boxed_id then mk(Cvar unboxed_id) else c
    | Cop(op, argv) -> mk(Cop(op, List.map subst argv))
    | Csequence(e1, e2) -> mk(Csequence(subst e1, subst e2))
    | Cifthenelse(e1, e2, e3) -> mk(Cifthenelse(subst e1, subst e2, subst e3))
    | Cswitch(arg, index, cases) ->
        mk(Cswitch(subst arg, index, Array.map subst cases))
    | Cloop e -> mk(Cloop(subst e))
    | Ccatch(nfail, ids, e1, e2) -> mk(Ccatch(nfail, ids, subst e1, subst e2))
    | Cexit (nfail, el) -> mk(Cexit (nfail, List.map subst el))
    | Ctrywith(e1, id, e2) -> mk(Ctrywith(subst e1, id, subst e2))
    | _ -> c in
  let res = subst exp in
  (res, !need_boxed, !assigned)

(* Translate an expression *)

let functions = (Queue.create() : (string * Ident.t list * ulambda) Queue.t)

let rec transl ulam =
  let mk = mkexpr_dbg ulam.ul_dbg in
  match ulam.ul_desc with
    Uvar id ->
      mk(Cvar id)
  | Uconst (sc, Some const_label) ->
      mk(Cconst_symbol const_label)
  | Uconst (sc, None) ->
      transl_constant sc
  | Uclosure(fundecls, []) ->
      let lbl = Compilenv.new_const_symbol() in
      constant_closures := (lbl, fundecls) :: !constant_closures;
      List.iter
        (fun f -> Queue.add (f.uf_label, f.uf_params, f.uf_body) functions)
        fundecls;
      mk(Cconst_symbol lbl)
  | Uclosure(fundecls, clos_vars) ->
      let block_size =
        fundecls_size fundecls + List.length clos_vars in
      let rec transl_fundecls pos = function
          [] ->
            List.map transl clos_vars
        | f :: rem ->
            Queue.add (f.uf_label, f.uf_params, f.uf_body) functions;
            let header =
              if pos = 0
              then mk(alloc_closure_header block_size)
              else mk(alloc_infix_header pos) in
            if f.uf_arity = 1 then
              header ::
              mk(Cconst_symbol f.uf_label) ::
              int_const f.uf_dbg 1 ::
              transl_fundecls (pos + 3) rem
            else
              header ::
              mk(Cconst_symbol(curry_function f.uf_arity)) ::
              int_const f.uf_dbg f.uf_arity ::
              mk(Cconst_symbol f.uf_label) ::
              transl_fundecls (pos + 4) rem in
      mk(Cop(Calloc, transl_fundecls 0 fundecls))
  | Uoffset(arg, offset) ->
      field_address (transl arg) offset
  | Udirect_apply(lbl, args) ->
      mk(Cop(Capply(typ_addr), mk(Cconst_symbol lbl) :: List.map transl args))
  | Ugeneric_apply(clos, [arg]) ->
      bind "fun" (transl clos) (fun clos ->
        mk(Cop(Capply(typ_addr), [get_field clos 0; transl arg; clos])))
  | Ugeneric_apply(clos, args) ->
      let arity = List.length args in
      let cargs = mk(Cconst_symbol(apply_function arity)) ::
        List.map transl (args @ [clos]) in
      mk(Cop(Capply typ_addr, cargs))
  | Usend(kind, met, obj, args) ->
      let call_met obj args clos =
        if args = [] then
          mk(Cop(Capply typ_addr, [get_field clos 0;obj;clos]))
        else
          let arity = List.length args + 1 in
          let cargs = mk(Cconst_symbol(apply_function arity)) :: obj ::
            (List.map transl args) @ [clos] in
          mk(Cop(Capply typ_addr, cargs))
      in
      bind "obj" (transl obj) (fun obj ->
        match kind, args with
          Self, _ ->
            bind "met" (lookup_label obj (transl met)) (call_met obj args)
        | Cached, cache :: pos :: args ->
            call_cached_method obj (transl met) (transl cache) (transl pos)
              (List.map transl args) ulam.ul_dbg
        | _ ->
            bind "met" (lookup_tag obj (transl met)) (call_met obj args))
  | Ulet(id, exp, body) ->
      begin match is_unboxed_number exp with
        No_unboxing ->
          mk(Clet(id, transl exp, transl body))
      | Boxed_float ->
          transl_unbox_let box_float unbox_float transl_unbox_float
                           id exp body
      | Boxed_integer bi ->
          transl_unbox_let (box_int bi) (unbox_int bi) (transl_unbox_int bi)
                           id exp body
      end
  | Uletrec(bindings, body) ->
      transl_letrec bindings (transl body)

  (* Primitives *)
  | Uprim(prim, args) ->
      begin match (simplif_primitive prim, args) with
        (Pgetglobal id, []) ->
          mk(Cconst_symbol (Ident.name id))
      | (Pmakeblock(tag, mut), []) ->
          transl_constant(Const_block(tag, []))
      | (Pmakeblock(tag, mut), args) ->
          make_alloc tag (List.map transl args) ulam.ul_dbg
      | (Pccall prim, args) ->
          if prim.prim_native_float then
            box_float
              (mk(Cop(Cextcall(prim.prim_native_name, typ_float, false),
                      List.map transl_unbox_float args)))
          else
            mk(Cop(Cextcall(Primitive.native_name prim, typ_addr, prim.prim_alloc),
                   List.map transl args))
      | (Pmakearray kind, []) ->
          transl_constant(Const_block(0, []))
      | (Pmakearray kind, args) ->
          begin match kind with
            Pgenarray ->
              mk(Cop(Cextcall("caml_make_array", typ_addr, true),
                     [make_alloc 0 (List.map transl args) ulam.ul_dbg]))
          | Paddrarray | Pintarray ->
              make_alloc 0 (List.map transl args) ulam.ul_dbg
          | Pfloatarray ->
              make_float_alloc Obj.double_array_tag
                (List.map transl_unbox_float args) ulam.ul_dbg
          end
      | (Pbigarrayref(unsafe, num_dims, elt_kind, layout), arg1 :: argl) ->
          let elt =
            bigarray_get unsafe elt_kind layout
              (transl arg1) (List.map transl argl) ulam.ul_dbg in
          begin match elt_kind with
            Pbigarray_float32 | Pbigarray_float64 -> box_float elt
          | Pbigarray_complex32 | Pbigarray_complex64 -> elt
          | Pbigarray_int32 -> box_int Pint32 elt
          | Pbigarray_int64 -> box_int Pint64 elt
          | Pbigarray_native_int -> box_int Pnativeint elt
          | Pbigarray_caml_int -> force_tag_int elt
          | _ -> tag_int elt
          end
      | (Pbigarrayset(unsafe, num_dims, elt_kind, layout), arg1 :: argl) ->
          let (argidx, argnewval) = split_last argl in
          return_unit(bigarray_set unsafe elt_kind layout
            (transl arg1)
            (List.map transl argidx)
            (match elt_kind with
              Pbigarray_float32 | Pbigarray_float64 ->
                transl_unbox_float argnewval
            | Pbigarray_complex32 | Pbigarray_complex64 -> transl argnewval
            | Pbigarray_int32 -> transl_unbox_int Pint32 argnewval
            | Pbigarray_int64 -> transl_unbox_int Pint64 argnewval
            | Pbigarray_native_int -> transl_unbox_int Pnativeint argnewval
            | _ -> untag_int (transl argnewval))
            ulam.ul_dbg)
      | (p, [arg]) ->
          transl_prim_1 p arg ulam.ul_dbg
      | (p, [arg1; arg2]) ->
          transl_prim_2 p arg1 arg2 ulam.ul_dbg
      | (p, [arg1; arg2; arg3]) ->
          transl_prim_3 p arg1 arg2 arg3 ulam.ul_dbg
      | (_, _) ->
          fatal_error "Cmmgen.transl:prim"
      end

  (* Control structures *)
  | Uswitch(arg, s) ->
      (* As in the bytecode interpreter, only matching against constants
         can be checked *)
      if Array.length s.us_index_blocks = 0 then
        mk(Cswitch
          (untag_int (transl arg),
           s.us_index_consts,
           Array.map transl s.us_actions_consts))
      else if Array.length s.us_index_consts = 0 then
        transl_switch (get_tag (transl arg))
          s.us_index_blocks s.us_actions_blocks
      else
        bind "switch" (transl arg) (fun arg ->
          mk(Cifthenelse(
            mk(Cop(Cand, [arg; mk(Cconst_int 1)])),
            transl_switch
              (untag_int arg) s.us_index_consts s.us_actions_consts,
            transl_switch
              (get_tag arg) s.us_index_blocks s.us_actions_blocks)))
  | Ustaticfail (nfail, args) ->
      mk(Cexit (nfail, List.map transl args))
  | Ucatch(nfail, [], body, handler) ->
      make_catch nfail (transl body) (transl handler)
  | Ucatch(nfail, ids, body, handler) ->
      mk(Ccatch(nfail, ids, transl body, transl handler))
  | Utrywith(body, exn, handler) ->
      mk(Ctrywith(transl body, exn, transl handler))
  | Uifthenelse({ul_desc=Uprim(Pnot, [arg])}, ifso, ifnot) ->
      transl (mkulambda_dbg ulam.ul_dbg (Uifthenelse(arg, ifnot, ifso)))
  | Uifthenelse(cond, ifso, {ul_desc=Ustaticfail (nfail, [])}) ->
      exit_if_false cond (transl ifso) nfail
  | Uifthenelse(cond, {ul_desc=Ustaticfail (nfail, [])}, ifnot) ->
      exit_if_true cond nfail (transl ifnot)
  | Uifthenelse({ul_desc=Uprim(Psequand, _)} as cond, ifso, ifnot) ->
      let raise_num = next_raise_count () in
      make_catch
        raise_num
        (exit_if_false cond (transl ifso) raise_num)
        (transl ifnot)
  | Uifthenelse({ul_desc=Uprim(Psequor, _)} as cond, ifso, ifnot) ->
      let raise_num = next_raise_count () in
      make_catch
        raise_num
        (exit_if_true cond raise_num (transl ifnot))
        (transl ifso)
  | Uifthenelse ({ul_desc=Uifthenelse (cond, condso, condnot)}, ifso, ifnot) ->
      let num_true = next_raise_count () in
      make_catch
        num_true
        (make_catch2
           (fun shared_false ->
             mk(Cifthenelse
                  (test_bool (transl cond),
                   exit_if_true condso num_true shared_false,
                   exit_if_true condnot num_true shared_false)))
           (transl ifnot))
        (transl ifso)
  | Uifthenelse(cond, ifso, ifnot) ->
      mk(Cifthenelse(test_bool(transl cond), transl ifso, transl ifnot))
  | Usequence(exp1, exp2) ->
      mk(Csequence(remove_unit(transl exp1), transl exp2))
  | Uwhile(cond, body) ->
      let raise_num = next_raise_count () in
      return_unit
        (mk(Ccatch
           (raise_num, [],
            mk(Cloop(exit_if_false cond (remove_unit(transl body)) raise_num)),
            mk(Ctuple []))))
  | Ufor(id, low, high, dir, body) ->
      let tst = match dir with Upto -> Cgt   | Downto -> Clt in
      let inc = match dir with Upto -> Caddi | Downto -> Csubi in
      let raise_num = next_raise_count () in
      let id_prev = Ident.rename id in
      return_unit
        (mk(Clet
          (id, transl low,
           bind_nonvar "bound" (transl high) (fun high ->
             mk(Ccatch
               (raise_num, [],
                mk(Cifthenelse
                  (mk(Cop(Ccmpi tst, [mk(Cvar id); high])), mk(Cexit (raise_num, [])),
                   mk(Cloop
                     (mk(Csequence
                        (remove_unit(transl body),
                         mk(Clet
                           (id_prev,
                            mk(Cvar id),
                            mk(Csequence
                              (mk(Cassign
                                 (id,
                                  mk(Cop(inc, [mk(Cvar id); mk(Cconst_int 2)])))),
                               mk(Cifthenelse
                                 (mk(Cop(Ccmpi Ceq, [mk(Cvar id_prev); high])),
                                  mk(Cexit (raise_num,[])),
                                  mk(Ctuple []))))))))))))),
                mk(Ctuple [])))))))
  | Uassign(id, exp) ->
      return_unit(mk(Cassign(id, transl exp)))

and transl_prim_1 p arg dbg =
  let mk = mkexpr_dbg dbg in
  match p with
  (* Generic operations *)
    Pidentity ->
      transl arg
  | Pignore ->
      return_unit(remove_unit (transl arg))
  (* Heap operations *)
  | Pfield n ->
      get_field (transl arg) n
  | Pfloatfield n ->
      let ptr = transl arg in
      box_float(
        mk(Cop(Cload Double_u,
            [if n = 0 then ptr
               else mk(Cop(Cadda, [ptr; mk(Cconst_int(n * size_float))]))])))
  (* Exceptions *)
  | Praise ->
      mk(Cop(Craise, [transl arg]))
  (* Integer operations *)
  | Pnegint ->
      mk(Cop(Csubi, [mk(Cconst_int 2); transl arg]))
  | Poffsetint n ->
      if no_overflow_lsl n then
        add_const (transl arg) (n lsl 1)
      else
        transl_prim_2 Paddint arg (mkulambda_dbg dbg (Uconst (Const_base(Const_int n), None))) dbg
  | Poffsetref n ->
      return_unit
        (bind "ref" (transl arg) (fun arg ->
          mk(Cop(Cstore Word,
              [arg; add_const (mk(Cop(Cload Word, [arg]))) (n lsl 1)]))))
  (* Floating-point operations *)
  | Pfloatofint ->
      box_float(mk(Cop(Cfloatofint, [untag_int(transl arg)])))
  | Pintoffloat ->
     tag_int(mk(Cop(Cintoffloat, [transl_unbox_float arg])))
  | Pnegfloat ->
      box_float(mk(Cop(Cnegf, [transl_unbox_float arg])))
  | Pabsfloat ->
      box_float(mk(Cop(Cabsf, [transl_unbox_float arg])))
  (* String operations *)
  | Pstringlength ->
      tag_int(string_length (transl arg))
  (* Array operations *)
  | Parraylength kind ->
      begin match kind with
        Pgenarray ->
          let len =
            if wordsize_shift = numfloat_shift then
              mk(Cop(Clsr, [header(transl arg); mk(Cconst_int wordsize_shift)]))
            else
              bind "header" (header(transl arg)) (fun hdr ->
                mk(Cifthenelse(is_addr_array_hdr hdr,
                            mk(Cop(Clsr, [hdr; mk(Cconst_int wordsize_shift)])),
                            mk(Cop(Clsr, [hdr; mk(Cconst_int numfloat_shift)]))))) in
          mk(Cop(Cor, [len; mk(Cconst_int 1)]))
      | Paddrarray | Pintarray ->
          mk(Cop(Cor, [addr_array_length(header(transl arg)); mk(Cconst_int 1)]))
      | Pfloatarray ->
          mk(Cop(Cor, [float_array_length(header(transl arg)); mk(Cconst_int 1)]))
      end
  (* Boolean operations *)
  | Pnot ->
      mk(Cop(Csubi, [mk(Cconst_int 4); transl arg])) (* 1 -> 3, 3 -> 1 *)
  (* Test integer/block *)
  | Pisint ->
      tag_int(mk(Cop(Cand, [transl arg; mk(Cconst_int 1)])))
  (* Boxed integers *)
  | Pbintofint bi ->
      box_int bi (untag_int (transl arg))
  | Pintofbint bi ->
      force_tag_int (transl_unbox_int bi arg)
  | Pcvtbint(bi1, bi2) ->
      box_int bi2 (transl_unbox_int bi1 arg)
  | Pnegbint bi ->
      box_int bi (mk(Cop(Csubi, [mk(Cconst_int 0); transl_unbox_int bi arg])))
  | _ ->
      fatal_error "Cmmgen.transl_prim_1"

and transl_prim_2 p arg1 arg2 dbg =
  let mk = mkexpr_dbg dbg in
  match p with
  (* Heap operations *)
    Psetfield(n, ptr) ->
      if ptr then
        return_unit(mk(Cop(Cextcall("caml_modify", typ_void, false),
                           [field_address (transl arg1) n; transl arg2])))
      else
        return_unit(set_field (transl arg1) n (transl arg2))
  | Psetfloatfield n ->
      let ptr = transl arg1 in
      return_unit(
        mk(Cop(Cstore Double_u,
            [if n = 0 then ptr
                       else mk(Cop(Cadda, [ptr; mk(Cconst_int(n * size_float))]));
                   transl_unbox_float arg2])))

  (* Boolean operations *)
  | Psequand ->
      mk(Cifthenelse(test_bool(transl arg1), transl arg2, mk(Cconst_int 1)))
      (* let id = Ident.create "res1" in
      Clet(id, transl arg1,
           Cifthenelse(test_bool(Cvar id), transl arg2, Cvar id)) *)
  | Psequor ->
      mk(Cifthenelse(test_bool(transl arg1), mk(Cconst_int 3), transl arg2))

  (* Integer operations *)
  | Paddint ->
      decr_int(add_int (transl arg1) (transl arg2))
  | Psubint ->
      incr_int(sub_int (transl arg1) (transl arg2))
  | Pmulint ->
      incr_int(mk(Cop(Cmuli, [decr_int(transl arg1); untag_int(transl arg2)])))
  | Pdivint ->
      tag_int(safe_divmod Cdivi (untag_int(transl arg1)) (untag_int(transl arg2)) dbg)
  | Pmodint ->
      tag_int(safe_divmod Cmodi (untag_int(transl arg1)) (untag_int(transl arg2)) dbg)
  | Pandint ->
      mk(Cop(Cand, [transl arg1; transl arg2]))
  | Porint ->
      mk(Cop(Cor, [transl arg1; transl arg2]))
  | Pxorint ->
      mk(Cop(Cor, [mk(Cop(Cxor, [ignore_low_bit_int(transl arg1);
                                 ignore_low_bit_int(transl arg2)]));
                   mk(Cconst_int 1)]))
  | Plslint ->
      incr_int(lsl_int (decr_int(transl arg1)) (untag_int(transl arg2)))
  | Plsrint ->
    mk(Cop(Cor, [mk(Cop(Clsr, [transl arg1; untag_int(transl arg2)]));
                 mk(Cconst_int 1)]))
  | Pasrint ->
    mk(Cop(Cor, [mk(Cop(Casr, [transl arg1; untag_int(transl arg2)]));
                 mk(Cconst_int 1)]))
  | Pintcomp cmp ->
      tag_int(mk(Cop(Ccmpi(transl_comparison cmp), [transl arg1; transl arg2])))
  | Pisout ->
      transl_isout (transl arg1) (transl arg2)
  (* Float operations *)
  | Paddfloat ->
      box_float(mk(Cop(Caddf,
                       [transl_unbox_float arg1; transl_unbox_float arg2])))
  | Psubfloat ->
      box_float(mk(Cop(Csubf,
                       [transl_unbox_float arg1; transl_unbox_float arg2])))
  | Pmulfloat ->
      box_float(mk(Cop(Cmulf,
                       [transl_unbox_float arg1; transl_unbox_float arg2])))
  | Pdivfloat ->
      box_float(mk(Cop(Cdivf,
                       [transl_unbox_float arg1; transl_unbox_float arg2])))
  | Pfloatcomp cmp ->
      tag_int(mk(Cop(Ccmpf(transl_comparison cmp),
                     [transl_unbox_float arg1; transl_unbox_float arg2])))

  (* String operations *)
  | Pstringrefu ->
      tag_int(mk(Cop(Cload Byte_unsigned,
                     [add_int (transl arg1) (untag_int(transl arg2))])))
  | Pstringrefs ->
      tag_int
        (bind "str" (transl arg1) (fun str ->
          bind "index" (untag_int (transl arg2)) (fun idx ->
            mk(Csequence(
              mk(Cop(Ccheckbound, [string_length str; idx])),
              mk(Cop(Cload Byte_unsigned, [add_int str idx])))))))

  (* Array operations *)
  | Parrayrefu kind ->
      begin match kind with
        Pgenarray ->
          bind "arr" (transl arg1) (fun arr ->
            bind "index" (transl arg2) (fun idx ->
              mk(Cifthenelse(is_addr_array_ptr arr,
                             addr_array_ref arr idx,
                             float_array_ref arr idx))))
      | Paddrarray | Pintarray ->
          addr_array_ref (transl arg1) (transl arg2)
      | Pfloatarray ->
          float_array_ref (transl arg1) (transl arg2)
      end
  | Parrayrefs kind ->
      begin match kind with
        Pgenarray ->
          bind "index" (transl arg2) (fun idx ->
            bind "arr" (transl arg1) (fun arr ->
              bind "header" (header arr) (fun hdr ->
                mk(Cifthenelse(is_addr_array_hdr hdr,
                               mk(Csequence(mk(Cop(Ccheckbound, [addr_array_length hdr; idx])),
                                            addr_array_ref arr idx)),
                               mk(Csequence(mk(Cop(Ccheckbound, [float_array_length hdr; idx])),
                                            float_array_ref arr idx)))))))
      | Paddrarray | Pintarray ->
          bind "index" (transl arg2) (fun idx ->
            bind "arr" (transl arg1) (fun arr ->
              mk(Csequence
                   (mk(Cop(Ccheckbound, [addr_array_length(header arr); idx])),
                    addr_array_ref arr idx))))
      | Pfloatarray ->
          box_float(
            bind "index" (transl arg2) (fun idx ->
              bind "arr" (transl arg1) (fun arr ->
                mk(Csequence
                     (mk(Cop(Ccheckbound, [float_array_length(header arr); idx])),
                      unboxed_float_array_ref arr idx)))))
      end

  (* Operations on bitvects *)
  | Pbittest ->
      bind "index" (untag_int(transl arg2)) (fun idx ->
        tag_int(
          mk(Cop(Cand, [mk(Cop(Clsr,
                               [mk(Cop(Cload Byte_unsigned,
                                       [add_int (transl arg1)
                                           (mk(Cop(Clsr, [idx; mk(Cconst_int 3)])))]));
                                mk(Cop(Cand, [idx; mk(Cconst_int 7)]))]));
                        mk(Cconst_int 1)]))))

  (* Boxed integers *)
  | Paddbint bi ->
      box_int bi (mk(Cop(Caddi,
                         [transl_unbox_int bi arg1; transl_unbox_int bi arg2])))
  | Psubbint bi ->
      box_int bi (mk(Cop(Csubi,
                         [transl_unbox_int bi arg1; transl_unbox_int bi arg2])))
  | Pmulbint bi ->
      box_int bi (mk(Cop(Cmuli,
                         [transl_unbox_int bi arg1; transl_unbox_int bi arg2])))
  | Pdivbint bi ->
      box_int bi (safe_divmod Cdivi
                      (transl_unbox_int bi arg1) (transl_unbox_int bi arg2)
                      dbg)
  | Pmodbint bi ->
      box_int bi (safe_divmod Cmodi
                      (transl_unbox_int bi arg1) (transl_unbox_int bi arg2)
                      dbg)
  | Pandbint bi ->
      box_int bi (mk(Cop(Cand,
                         [transl_unbox_int bi arg1; transl_unbox_int bi arg2])))
  | Porbint bi ->
      box_int bi (mk(Cop(Cor,
                         [transl_unbox_int bi arg1; transl_unbox_int bi arg2])))
  | Pxorbint bi ->
      box_int bi (mk(Cop(Cxor,
                         [transl_unbox_int bi arg1; transl_unbox_int bi arg2])))
  | Plslbint bi ->
      box_int bi (mk(Cop(Clsl,
                         [transl_unbox_int bi arg1; untag_int(transl arg2)])))
  | Plsrbint bi ->
      box_int bi (mk(Cop(Clsr,
                         [make_unsigned_int bi (transl_unbox_int bi arg1);
                          untag_int(transl arg2)])))
  | Pasrbint bi ->
      box_int bi (mk(Cop(Casr,
                         [transl_unbox_int bi arg1; untag_int(transl arg2)])))
  | Pbintcomp(bi, cmp) ->
      tag_int (mk(Cop(Ccmpi(transl_comparison cmp),
                      [transl_unbox_int bi arg1; transl_unbox_int bi arg2])))
  | _ ->
      fatal_error "Cmmgen.transl_prim_2"

and transl_prim_3 p arg1 arg2 arg3 dbg =
  let mk = mkexpr_dbg dbg in
  match p with
  (* String operations *)
    Pstringsetu ->
      return_unit(mk(Cop(Cstore Byte_unsigned,
                         [add_int (transl arg1) (untag_int(transl arg2));
                          untag_int(transl arg3)])))
  | Pstringsets ->
      return_unit
        (bind "str" (transl arg1) (fun str ->
          bind "index" (untag_int (transl arg2)) (fun idx ->
            mk(Csequence(
              mk(Cop(Ccheckbound, [string_length str; idx])),
              mk(Cop(Cstore Byte_unsigned,
                  [add_int str idx; untag_int(transl arg3)])))))))

  (* Array operations *)
  | Parraysetu kind ->
      return_unit(begin match kind with
        Pgenarray ->
          bind "newval" (transl arg3) (fun newval ->
            bind "index" (transl arg2) (fun index ->
              bind "arr" (transl arg1) (fun arr ->
                mk(Cifthenelse(is_addr_array_ptr arr,
                               addr_array_set arr index newval,
                               float_array_set arr index (unbox_float newval))))))
      | Paddrarray ->
          addr_array_set (transl arg1) (transl arg2) (transl arg3)
      | Pintarray ->
          int_array_set (transl arg1) (transl arg2) (transl arg3)
      | Pfloatarray ->
          float_array_set (transl arg1) (transl arg2) (transl_unbox_float arg3)
      end)
  | Parraysets kind ->
      return_unit(begin match kind with
        Pgenarray ->
          bind "newval" (transl arg3) (fun newval ->
            bind "index" (transl arg2) (fun idx ->
              bind "arr" (transl arg1) (fun arr ->
                bind "header" (header arr) (fun hdr ->
                  mk(Cifthenelse
                       (is_addr_array_hdr hdr,
                        mk(Csequence
                          (mk(Cop(Ccheckbound, [addr_array_length hdr; idx])),
                           addr_array_set arr idx newval)),
                        mk(Csequence
                          (mk(Cop(Ccheckbound, [float_array_length hdr; idx])),
                           float_array_set arr idx (unbox_float newval)))))))))
      | Paddrarray ->
          bind "index" (transl arg2) (fun idx ->
            bind "arr" (transl arg1) (fun arr ->
              mk(Csequence
                (mk(Cop(Ccheckbound,[addr_array_length(header arr); idx])),
                 addr_array_set arr idx (transl arg3)))))
      | Pintarray ->
          bind "index" (transl arg2) (fun idx ->
            bind "arr" (transl arg1) (fun arr ->
              mk(Csequence
                (mk(Cop(Ccheckbound, [addr_array_length(header arr); idx])),
                 int_array_set arr idx (transl arg3)))))
      | Pfloatarray ->
          bind "index" (transl arg2) (fun idx ->
            bind "arr" (transl arg1) (fun arr ->
              mk(Csequence
                (mk(Cop(Ccheckbound, [float_array_length(header arr);idx])),
                 float_array_set arr idx (transl_unbox_float arg3)))))
      end)
  | _ ->
    fatal_error "Cmmgen.transl_prim_3"

and transl_unbox_float ulam =
  let mk = mkexpr_dbg ulam.ul_dbg in
  match ulam.ul_desc with
    Uconst(Const_base(Const_float f), _) -> mk(Cconst_float f)
  | _ -> unbox_float(transl ulam)

and transl_unbox_int bi ulam =
  let mk = mkexpr_dbg ulam.ul_dbg in
  match ulam.ul_desc with
    Uconst(Const_base(Const_int32 n), _) ->
      mk(Cconst_natint (Nativeint.of_int32 n))
  | Uconst(Const_base(Const_nativeint n), _) ->
      mk(Cconst_natint n)
  | Uconst(Const_base(Const_int64 n), _) ->
      assert (size_int = 8); mk(Cconst_natint (Int64.to_nativeint n))
  | Uprim(Pbintofint bi', [{ul_desc=Uconst(Const_base(Const_int i),_)}]) when bi = bi' ->
      mk(Cconst_int i)
  | _ -> unbox_int bi (transl ulam)

and transl_unbox_let box_fn unbox_fn transl_unbox_fn id exp body =
  let unboxed_id = Ident.create (Ident.name id) in
  let trbody1 = transl body in
  let (trbody2, need_boxed, is_assigned) =
    subst_boxed_number unbox_fn id unboxed_id trbody1 in
  let mk = mkexpr_dbg exp.ul_dbg in
  if need_boxed && is_assigned then
    mk(Clet(id, transl exp, trbody1))
  else
    mk(Clet(unboxed_id, transl_unbox_fn exp,
            if need_boxed
            then mk(Clet(id, box_fn(mk(Cvar unboxed_id)), trbody2))
            else trbody2))

and make_catch ncatch body handler =
  let mk = mkexpr_dbg body.cmm_dbg in
  match body.cmm_desc with
  | Cexit (nexit,[]) when nexit=ncatch -> handler
  | _ ->  mk(Ccatch (ncatch, [], body, handler))

and make_catch2 mk_body handler =
  let mk = mkexpr_dbg handler.cmm_dbg in
  match handler.cmm_desc with
  | Cexit (_,[])|Ctuple []|Cconst_int _|Cconst_pointer _ -> mk_body handler
  | _ ->
    let nfail = next_raise_count () in
    make_catch
      nfail
      (mk_body (mk(Cexit (nfail,[]))))
      handler

and exit_if_true cond nfail otherwise =
  let mk = mkexpr_dbg cond.ul_dbg in
  match cond.ul_desc with
  | Uconst (Const_pointer 0, _) -> otherwise
  | Uconst (Const_pointer 1, _) -> mk(Cexit (nfail,[]))
  | Uprim(Psequor, [arg1; arg2]) ->
      exit_if_true arg1 nfail (exit_if_true arg2 nfail otherwise)
  | Uprim(Psequand, _) ->
      begin match otherwise.cmm_desc with
      | Cexit (raise_num,[]) ->
          exit_if_false cond (mk(Cexit (nfail,[]))) raise_num
      | _ ->
          let raise_num = next_raise_count () in
          make_catch
            raise_num
            (exit_if_false cond (mk(Cexit (nfail,[]))) raise_num)
            otherwise
      end
  | Uprim(Pnot, [arg]) ->
      exit_if_false arg otherwise nfail
  | Uifthenelse (cond, ifso, ifnot) ->
      make_catch2
        (fun shared ->
          mk(Cifthenelse
               (test_bool (transl cond),
                exit_if_true ifso nfail shared,
                exit_if_true ifnot nfail shared)))
        otherwise
  | _ ->
      mk(Cifthenelse(test_bool(transl cond), mk(Cexit (nfail, [])), otherwise))

and exit_if_false cond otherwise nfail =
  let mk = mkexpr_dbg cond.ul_dbg in
  match cond.ul_desc with
  | Uconst (Const_pointer 0, _) -> mk(Cexit (nfail,[]))
  | Uconst (Const_pointer 1, _) -> otherwise
  | Uprim(Psequand, [arg1; arg2]) ->
      exit_if_false arg1 (exit_if_false arg2 otherwise nfail) nfail
  | Uprim(Psequor, _) ->
      begin match otherwise.cmm_desc with
      | Cexit (raise_num,[]) ->
          exit_if_true cond raise_num (mk(Cexit (nfail,[])))
      | _ ->
          let raise_num = next_raise_count () in
          make_catch
            raise_num
            (exit_if_true cond raise_num (mk(Cexit (nfail,[]))))
            otherwise
      end
  | Uprim(Pnot, [arg]) ->
      exit_if_true arg nfail otherwise
  | Uifthenelse (cond, ifso, ifnot) ->
      make_catch2
        (fun shared ->
          mk(Cifthenelse
               (test_bool (transl cond),
                exit_if_false ifso shared nfail,
                exit_if_false ifnot shared nfail)))
        otherwise
  | _ ->
      mk(Cifthenelse(test_bool(transl cond), otherwise, mk(Cexit (nfail, []))))

and transl_switch arg index cases = match Array.length cases with
| 0 -> fatal_error "Cmmgen.transl_switch"
| 1 -> transl cases.(0)
| _ ->
    let n_index = Array.length index in
    let actions = Array.map transl cases in

    let inters = ref []
    and this_high = ref (n_index-1)
    and this_low = ref (n_index-1)
    and this_act = ref index.(n_index-1) in
    for i = n_index-2 downto 0 do
      let act = index.(i) in
      if act = !this_act then
        decr this_low
      else begin
        inters := (!this_low, !this_high, !this_act) :: !inters ;
        this_high := i ;
        this_low := i ;
        this_act := act
      end
    done ;
    inters := (0, !this_high, !this_act) :: !inters ;
    let mk = mkexpr_dbg arg.cmm_dbg in
    bind "switcher" arg
      (fun a ->
        SwitcherBlocks.zyva
          (0,n_index-1)
          (fun i -> mk(Cconst_int i))
          a
          (Array.of_list !inters) actions)

and transl_letrec bindings cont =
  let mk = mkexpr in
  let bsz = List.map (fun (id, exp) -> (id, exp, expr_size exp)) bindings in
  let rec init_blocks = function
    | [] -> fill_nonrec bsz
    | (id, exp, RHS_block sz) :: rem ->
        mk(Clet
             (id,
              mk(Cop(Cextcall("caml_alloc_dummy", typ_addr, true), [int_const Debuginfo.none sz])),
              init_blocks rem))
    | (id, exp, RHS_nonrec) :: rem ->
        mk(Clet (id, mk(Cconst_int 0), init_blocks rem))
  and fill_nonrec = function
    | [] -> fill_blocks bsz
    | (id, exp, RHS_block sz) :: rem -> fill_nonrec rem
    | (id, exp, RHS_nonrec) :: rem ->
        mk(Clet (id, transl exp, fill_nonrec rem))
  and fill_blocks = function
    | [] -> cont
    | (id, exp, RHS_block _) :: rem ->
        mk(Csequence
             (mk(Cop(Cextcall("caml_update_dummy", typ_void, false), [mk(Cvar id); transl exp])),
              fill_blocks rem))
    | (id, exp, RHS_nonrec) :: rem ->
        fill_blocks rem
  in init_blocks bsz

(* Translate a function definition *)

let transl_function lbl params body =
  Cfunction {fun_name = lbl;
             fun_args = List.map (fun id -> (id, typ_addr)) params;
             fun_body = transl body;
             fun_fast = !Clflags.optimize_for_speed}

(* Translate all function definitions *)

module StringSet =
  Set.Make(struct
    type t = string
    let compare = compare
  end)

let rec transl_all_functions already_translated cont =
  try
    let (lbl, params, body) = Queue.take functions in
    if StringSet.mem lbl already_translated then
      transl_all_functions already_translated cont
    else begin
      transl_all_functions (StringSet.add lbl already_translated)
                           (transl_function lbl params body :: cont)
    end
  with Queue.Empty ->
    cont

(* Emit structured constants *)

let immstrings = Hashtbl.create 17

let rec emit_constant symb cst cont =
  match cst with
    Const_base(Const_float s) ->
      Cint(float_header) :: Cdefine_symbol symb :: Cdouble s :: cont
  | Const_base(Const_string s) | Const_immstring s ->
      Cint(string_header (String.length s)) ::
      Cdefine_symbol symb ::
      emit_string_constant s cont
  | Const_base(Const_int32 n) ->
      Cint(boxedint32_header) :: Cdefine_symbol symb ::
      emit_boxed_int32_constant n cont
  | Const_base(Const_int64 n) ->
      Cint(boxedint64_header) :: Cdefine_symbol symb ::
      emit_boxed_int64_constant n cont
  | Const_base(Const_nativeint n) ->
      Cint(boxedintnat_header) :: Cdefine_symbol symb ::
      emit_boxed_nativeint_constant n cont
  | Const_block(tag, fields) ->
      let (emit_fields, cont1) = emit_constant_fields fields cont in
      Cint(block_header tag (List.length fields)) ::
      Cdefine_symbol symb ::
      emit_fields @ cont1
  | Const_float_array(fields) ->
      Cint(floatarray_header (List.length fields)) ::
      Cdefine_symbol symb ::
      Misc.map_end (fun f -> Cdouble f) fields cont
  | _ -> fatal_error "gencmm.emit_constant"

and emit_constant_fields fields cont =
  match fields with
    [] -> ([], cont)
  | f1 :: fl ->
      let (data1, cont1) = emit_constant_field f1 cont in
      let (datal, contl) = emit_constant_fields fl cont1 in
      (data1 :: datal, contl)

and emit_constant_field field cont =
  match field with
    Const_base(Const_int n) ->
      (Cint(Nativeint.add (Nativeint.shift_left (Nativeint.of_int n) 1) 1n),
       cont)
  | Const_base(Const_char c) ->
      (Cint(Nativeint.of_int(((Char.code c) lsl 1) + 1)), cont)
  | Const_base(Const_float s) ->
      let lbl = Compilenv.new_const_label() in
      (Clabel_address lbl,
       Cint(float_header) :: Cdefine_label lbl :: Cdouble s :: cont)
  | Const_base(Const_string s) ->
      let lbl = Compilenv.new_const_label() in
      (Clabel_address lbl,
       Cint(string_header (String.length s)) :: Cdefine_label lbl ::
       emit_string_constant s cont)
  | Const_immstring s ->
      begin try
        (Clabel_address (Hashtbl.find immstrings s), cont)
      with Not_found ->
        let lbl = Compilenv.new_const_label() in
        Hashtbl.add immstrings s lbl;
        (Clabel_address lbl,
         Cint(string_header (String.length s)) :: Cdefine_label lbl ::
         emit_string_constant s cont)
      end
  | Const_base(Const_int32 n) ->
      let lbl = Compilenv.new_const_label() in
      (Clabel_address lbl,
       Cint(boxedint32_header) :: Cdefine_label lbl ::
       emit_boxed_int32_constant n cont)
  | Const_base(Const_int64 n) ->
      let lbl = Compilenv.new_const_label() in
      (Clabel_address lbl,
       Cint(boxedint64_header) :: Cdefine_label lbl ::
       emit_boxed_int64_constant n cont)
  | Const_base(Const_nativeint n) ->
      let lbl = Compilenv.new_const_label() in
      (Clabel_address lbl,
       Cint(boxedintnat_header) :: Cdefine_label lbl ::
       emit_boxed_nativeint_constant n cont)
  | Const_pointer n ->
      (Cint(Nativeint.add (Nativeint.shift_left (Nativeint.of_int n) 1) 1n),
       cont)
  | Const_block(tag, fields) ->
      let lbl = Compilenv.new_const_label() in
      let (emit_fields, cont1) = emit_constant_fields fields cont in
      (Clabel_address lbl,
       Cint(block_header tag (List.length fields)) :: Cdefine_label lbl ::
       emit_fields @ cont1)
  | Const_float_array(fields) ->
      let lbl = Compilenv.new_const_label() in
      (Clabel_address lbl,
       Cint(floatarray_header (List.length fields)) :: Cdefine_label lbl ::
       Misc.map_end (fun f -> Cdouble f) fields cont)

and emit_string_constant s cont =
  let n = size_int - 1 - (String.length s) mod size_int in
  Cstring s :: Cskip n :: Cint8 n :: cont

and emit_boxed_int32_constant n cont =
  let n = Nativeint.of_int32 n in
  if size_int = 8 then
    Csymbol_address("caml_int32_ops") :: Cint32 n :: Cint32 0n :: cont
  else
    Csymbol_address("caml_int32_ops") :: Cint n :: cont

and emit_boxed_nativeint_constant n cont =
  Csymbol_address("caml_nativeint_ops") :: Cint n :: cont

and emit_boxed_int64_constant n cont =
  let lo = Int64.to_nativeint n in
  if size_int = 8 then
    Csymbol_address("caml_int64_ops") :: Cint lo :: cont
  else begin
    let hi = Int64.to_nativeint (Int64.shift_right n 32) in
    if big_endian then
      Csymbol_address("caml_int64_ops") :: Cint hi :: Cint lo :: cont
    else
      Csymbol_address("caml_int64_ops") :: Cint lo :: Cint hi :: cont
  end

(* Emit constant closures *)

let emit_constant_closure symb fundecls cont =
  match fundecls with
    [] -> assert false
  | f1 :: remainder ->
      let rec emit_others pos = function
        [] -> cont
      | f2 :: rem ->
          if f2.uf_arity = 1 then
            Cint(infix_header pos) ::
            Csymbol_address f2.uf_label ::
            Cint 3n ::
            emit_others (pos + 3) rem
          else
            Cint(infix_header pos) ::
            Csymbol_address(curry_function f2.uf_arity) ::
            Cint(Nativeint.of_int (f2.uf_arity lsl 1 + 1)) ::
            Csymbol_address f2.uf_label ::
            emit_others (pos + 4) rem in
      Cint(closure_header (fundecls_size fundecls)) ::
      Cdefine_symbol symb ::
      if f1.uf_arity = 1 then
        Csymbol_address f1.uf_label ::
        Cint 3n ::
        emit_others 3 remainder
      else
        Csymbol_address(curry_function f1.uf_arity) ::
        Cint(Nativeint.of_int (f1.uf_arity lsl 1 + 1)) ::
        Csymbol_address f1.uf_label ::
        emit_others 4 remainder

(* Emit all structured constants *)

let emit_all_constants cont =
  let c = ref cont in
  List.iter
    (fun (lbl, global, cst) -> 
       let cst = emit_constant lbl cst [] in
       let cst = if global then 
	 Cglobal_symbol lbl :: cst
       else cst in
	 c:= Cdata(cst):: !c)
    (Compilenv.structured_constants());
(*  structured_constants := []; done in Compilenv.reset() *)
  Hashtbl.clear immstrings;   (* PR#3979 *)
  List.iter
    (fun (symb, fundecls) ->
        c := Cdata(emit_constant_closure symb fundecls []) :: !c)
    !constant_closures;
  constant_closures := [];
  !c

(* Translate a compilation unit *)

let compunit size ulam =
  let glob = Compilenv.make_symbol None in
  let init_code = transl ulam in
  let c1 = [Cfunction {fun_name = Compilenv.make_symbol (Some "entry");
                       fun_args = [];
                       fun_body = init_code; fun_fast = false}] in
  let c2 = transl_all_functions StringSet.empty c1 in
  let c3 = emit_all_constants c2 in
  Cdata [Cint(block_header 0 size);
         Cglobal_symbol glob;
         Cdefine_symbol glob;
         Cskip(size * size_addr)] :: c3

(*
CAMLprim value caml_cache_public_method (value meths, value tag, value *cache)
{
  int li = 3, hi = Field(meths,0), mi;
  while (li < hi) { // no need to check the 1st time
    mi = ((li+hi) >> 1) | 1;
    if (tag < Field(meths,mi)) hi = mi-2;
    else li = mi;
  }
  *cache = (li-3)*sizeof(value)+1;
  return Field (meths, li-1);
}
*)

let cache_public_method meths tag cache =
  let mk = mkexpr in
  let raise_num = next_raise_count () in
  let li = Ident.create "li" and hi = Ident.create "hi"
  and mi = Ident.create "mi" and tagged = Ident.create "tagged" in
  mk(Clet (
  li, mk(Cconst_int 3),
  mk(Clet (
  hi, mk(Cop(Cload Word, [meths])),
  mk(Csequence(
  mk(Ccatch
    (raise_num, [],
     mk(Cloop
       (mk(Clet(
        mi,
        mk(Cop(Cor,
            [mk(Cop(Clsr, [mk(Cop(Caddi, [mk(Cvar li); mk(Cvar hi)])); mk(Cconst_int 1)]));
             mk(Cconst_int 1)])),
        mk(Csequence(
        mk(Cifthenelse
          (mk(Cop (Ccmpi Clt,
                [tag;
                 mk(Cop(Cload Word,
                     [mk(Cop(Cadda,
                          [meths; lsl_const (mk(Cvar mi)) log2_size_addr]))]))])),
           mk(Cassign(hi, mk(Cop(Csubi, [mk(Cvar mi); mk(Cconst_int 2)])))),
           mk(Cassign(li, mk(Cvar mi))))),
        mk(Cifthenelse
          (mk(Cop(Ccmpi Cge, [mk(Cvar li); mk(Cvar hi)])), mk(Cexit (raise_num, [])),
           mk(Ctuple []))))))))),
     mk(Ctuple []))),
  mk(Clet (
  tagged, mk(Cop(Cadda, [lsl_const (mk(Cvar li)) log2_size_addr;
                      mk(Cconst_int(1 - 3 * size_addr))])),
  mk(Csequence(mk(Cop (Cstore Word, [cache; mk(Cvar tagged)])),
               mk(Cvar tagged)))))))))))

(* Generate an application function:
     (defun caml_applyN (a1 ... aN clos)
       (if (= clos.arity N)
         (app clos.direct a1 ... aN clos)
         (let (clos1 (app clos.code a1 clos)
               clos2 (app clos1.code a2 clos)
               ...
               closN-1 (app closN-2.code aN-1 closN-2))
           (app closN-1.code aN closN-1))))
*)

let apply_function_body arity =
  let arg = Array.create arity (Ident.create "arg") in
  for i = 1 to arity - 1 do arg.(i) <- Ident.create "arg" done;
  let clos = Ident.create "clos" in
  let mk = mkexpr in
  let rec app_fun clos n =
    if n = arity-1 then
      mk(Cop(Capply typ_addr,
          [get_field (mk(Cvar clos)) 0; mk(Cvar arg.(n)); mk(Cvar clos)]))
    else begin
      let newclos = Ident.create "clos" in
      mk(Clet(newclos,
           mk(Cop(Capply typ_addr,
                  [get_field (mk(Cvar clos)) 0; mk(Cvar arg.(n)); mk(Cvar clos)])),
              app_fun newclos (n+1)))
    end in
  let args = Array.to_list arg in
  let all_args = args @ [clos] in
  (args, clos,
   if arity = 1 then app_fun clos 0 else
   mk(Cifthenelse(
   mk(Cop(Ccmpi Ceq, [get_field (mk(Cvar clos)) 1; int_const Debuginfo.none arity])),
   mk(Cop(Capply typ_addr,
      get_field (mk(Cvar clos)) 2 :: List.map (fun s -> mk(Cvar s)) all_args)),
   app_fun clos 0)))

let send_function arity =
  let (args, clos', body) = apply_function_body (1+arity) in
  let cache = Ident.create "cache"
  and obj = List.hd args
  and tag = Ident.create "tag" in
  let mk = mkexpr in
  let clos =
    let cache = mk(Cvar cache)
    and obj = mk(Cvar obj)
    and tag = mk(Cvar tag) in
    let meths = Ident.create "meths" and cached = Ident.create "cached" in
    let real = Ident.create "real" in
    let mask = get_field (mk(Cvar meths)) 1 in
    let cached_pos = mk(Cvar cached) in
    let tag_pos = mk(Cop(Cadda, [mk(Cop (Cadda, [cached_pos; mk(Cvar meths)]));
                                 mk(Cconst_int(3*size_addr-1))])) in
    let tag' = mk(Cop(Cload Word, [tag_pos])) in
    mk(Clet (
    meths, mk(Cop(Cload Word, [obj])),
    mk(Clet (
    cached, mk(Cop(Cand, [mk(Cop(Cload Word, [cache])); mask])),
    mk(Clet (
    real,
    mk(Cifthenelse(mk(Cop(Ccmpa Cne, [tag'; tag])),
                   cache_public_method (mk(Cvar meths)) tag cache,
                   cached_pos)),
    mk(Cop(Cload Word,
           [mk(Cop(Cadda,
                   [mk(Cop (Cadda, [mk(Cvar real); mk(Cvar meths)]));
                    mk(Cconst_int(2*size_addr-1))]))]))))))))
  in
  let body = mk(Clet(clos', clos, body)) in
  let fun_args =
    [obj, typ_addr; tag, typ_int; cache, typ_addr]
    @ List.map (fun id -> (id, typ_addr)) (List.tl args) in
  Cfunction
   {fun_name = "caml_send" ^ string_of_int arity;
    fun_args = fun_args;
    fun_body = body;
    fun_fast = true}

let apply_function arity =
  let (args, clos, body) = apply_function_body arity in
  let all_args = args @ [clos] in
  Cfunction
   {fun_name = "caml_apply" ^ string_of_int arity;
    fun_args = List.map (fun id -> (id, typ_addr)) all_args;
    fun_body = body;
    fun_fast = true}

(* Generate tuplifying functions:
      (defun caml_tuplifyN (arg clos)
        (app clos.direct #0(arg) ... #N-1(arg) clos)) *)

let tuplify_function arity =
  let arg = Ident.create "arg" in
  let clos = Ident.create "clos" in
  let mk = mkexpr in
  let rec access_components i =
    if i >= arity
    then []
    else get_field (mk(Cvar arg)) i :: access_components(i+1) in
  Cfunction
   {fun_name = "caml_tuplify" ^ string_of_int arity;
    fun_args = [arg, typ_addr; clos, typ_addr];
    fun_body =
      mk(Cop(Capply typ_addr,
             get_field (mk(Cvar clos)) 2 :: access_components 0 @ [mk(Cvar clos)]));
    fun_fast = true}

(* Generate currying functions:
      (defun caml_curryN (arg clos)
         (alloc HDR caml_curryN_1 <arity (N-1)> caml_curry_N_1_app arg clos))
      (defun caml_curryN_1 (arg clos)
         (alloc HDR caml_curryN_2 <arity (N-2)> caml_curry_N_2_app arg clos))
      ...
      (defun caml_curryN_N-1 (arg clos)
         (let (closN-2 clos.vars[1]
               closN-3 closN-2.vars[1]
               ...
               clos1 clos2.vars[1]
               clos clos1.vars[1])
           (app clos.direct
                clos1.vars[0] ... closN-2.vars[0] clos.vars[0] arg clos)))
    Special "shortcut" functions are also generated to handle the
    case where a partially applied function is applied to all remaining
    arguments in one go.  For instance:
      (defun caml_curry_N_1_app (arg2 ... argN clos)
        (let clos' clos.vars[1]
           (app clos'.direct clos.vars[0] arg2 ... argN clos')))
*)

let final_curry_function arity =
  let last_arg = Ident.create "arg" in
  let last_clos = Ident.create "clos" in
  let mk = mkexpr in
  let rec curry_fun args clos n =
    if n = 0 then
      mk(Cop(Capply typ_addr,
             get_field (mk(Cvar clos)) 2 ::
               args @ [mk(Cvar last_arg); mk(Cvar clos)]))
    else
      if n = arity - 1 then
	begin
      let newclos = Ident.create "clos" in
      mk(Clet(newclos,
           get_field (mk(Cvar clos)) 3,
           curry_fun (get_field (mk(Cvar clos)) 2 :: args) newclos (n-1)))
	end else
	begin
	  let newclos = Ident.create "clos" in
	  mk(Clet(newclos,
               get_field (mk(Cvar clos)) 4,
               curry_fun (get_field (mk(Cvar clos)) 3 :: args) newclos (n-1)))
    end in
  Cfunction
   {fun_name = "caml_curry" ^ string_of_int arity ^
               "_" ^ string_of_int (arity-1);
    fun_args = [last_arg, typ_addr; last_clos, typ_addr];
    fun_body = curry_fun [] last_clos (arity-1);
    fun_fast = true}

let rec intermediate_curry_functions arity num =
  if num = arity - 1 then
    [final_curry_function arity]
  else begin
    let name1 = "caml_curry" ^ string_of_int arity in
    let name2 = if num = 0 then name1 else name1 ^ "_" ^ string_of_int num in
    let arg = Ident.create "arg" and clos = Ident.create "clos" in
    let mk = mkexpr in
    Cfunction
     {fun_name = name2;
      fun_args = [arg, typ_addr; clos, typ_addr];
      fun_body =
	 if arity - num > 2 then
	   mk(Cop(Calloc,
               [mk(alloc_closure_header 5);
                mk(Cconst_symbol(name1 ^ "_" ^ string_of_int (num+1)));
                int_const Debuginfo.none (arity - num - 1);
                mk(Cconst_symbol(name1 ^ "_" ^ string_of_int (num+1) ^ "_app"));
		mk(Cvar arg); mk(Cvar clos)]))
	 else
	   mk(Cop(Calloc,
                     [mk(alloc_closure_header 4);
                      mk(Cconst_symbol(name1 ^ "_" ^ string_of_int (num+1)));
                      int_const Debuginfo.none 1; mk(Cvar arg); mk(Cvar clos)]));
      fun_fast = true}
    ::
      (if arity - num > 2 then
	  let rec iter i =
	    if i <= arity then
	      let arg = Ident.create (Printf.sprintf "arg%d" i) in
	      (arg, typ_addr) :: iter (i+1)
	    else []
	  in
	  let direct_args = iter (num+2) in
	  let rec iter i args clos =
	    if i = 0 then
	      mk(Cop(Capply typ_addr,
		  (get_field (mk(Cvar clos)) 2) :: args @ [mk(Cvar clos)]))
	    else
	      let newclos = Ident.create "clos" in
	      mk(Clet(newclos,
		   get_field (mk(Cvar clos)) 4,
		   iter (i-1) (get_field (mk(Cvar clos)) 3 :: args) newclos))
	  in
	  let cf =
	    Cfunction
	      {fun_name = name1 ^ "_" ^ string_of_int (num+1) ^ "_app";
	       fun_args = direct_args @ [clos, typ_addr];
	       fun_body = iter (num+1)
		  (List.map (fun (arg,_) -> mk(Cvar arg)) direct_args) clos;
	       fun_fast = true}
	  in
	  cf :: intermediate_curry_functions arity (num+1)
       else
	  intermediate_curry_functions arity (num+1))
  end

let curry_function arity =
  if arity >= 0
  then intermediate_curry_functions arity 0
  else [tuplify_function (-arity)]


module IntSet = Set.Make(
  struct
    type t = int
    let compare = compare
  end)

let default_apply = IntSet.add 2 (IntSet.add 3 IntSet.empty)
  (* These apply funs are always present in the main program because
     the run-time system needs them (cf. asmrun/<arch>.S) . *)

let generic_functions shared units =
  let (apply,send,curry) =
    List.fold_left
      (fun (apply,send,curry) ui ->
         List.fold_right IntSet.add ui.ui_apply_fun apply,
         List.fold_right IntSet.add ui.ui_send_fun send,
         List.fold_right IntSet.add ui.ui_curry_fun curry)
      (IntSet.empty,IntSet.empty,IntSet.empty)
      units in
  let apply = if shared then apply else IntSet.union apply default_apply in
  let accu = IntSet.fold (fun n accu -> apply_function n :: accu) apply [] in
  let accu = IntSet.fold (fun n accu -> send_function n :: accu) send accu in
  IntSet.fold (fun n accu -> curry_function n @ accu) curry accu

(* Generate the entry point *)

let entry_point namelist =
  let mk = mkexpr in
  let incr_global_inited =
    mk(Cop(Cstore Word,
           [mk(Cconst_symbol "caml_globals_inited");
            mk(Cop(Caddi, [mk(Cop(Cload Word, [mk(Cconst_symbol "caml_globals_inited")]));
                           mk(Cconst_int 1)]))])) in
  let body =
    List.fold_right
      (fun name next ->
        let entry_sym = Compilenv.make_symbol ~unitname:name (Some "entry") in
        mk(Csequence(mk(Cop(Capply typ_void,
                            [mk(Cconst_symbol entry_sym)])),
                     mk(Csequence(incr_global_inited, next)))))
      namelist (mk(Cconst_int 1)) in
  Cfunction {fun_name = "caml_program";
             fun_args = [];
             fun_body = body;
             fun_fast = false}

(* Generate the table of globals *)

let cint_zero = Cint 0n

let global_table namelist =
  let mksym name =
    Csymbol_address (Compilenv.make_symbol ~unitname:name None)
  in
  Cdata(Cglobal_symbol "caml_globals" ::
        Cdefine_symbol "caml_globals" ::
        List.map mksym namelist @
        [cint_zero])

let reference_symbols namelist =
  let mksym name = Csymbol_address name in
  Cdata(List.map mksym namelist)

let global_data name v =
  Cdata(Cglobal_symbol name ::
          emit_constant name
          (Const_base (Const_string (Marshal.to_string v []))) [])

let globals_map v = global_data "caml_globals_map" v

(* Generate the master table of frame descriptors *)

let frame_table namelist =
  let mksym name =
    Csymbol_address (Compilenv.make_symbol ~unitname:name (Some "frametable"))
  in
  Cdata(Cglobal_symbol "caml_frametable" ::
        Cdefine_symbol "caml_frametable" ::
        List.map mksym namelist
        @ [cint_zero])

(* Generate the table of module data and code segments *)

let segment_table namelist symbol begname endname =
  let addsyms name lst =
    Csymbol_address (Compilenv.make_symbol ~unitname:name (Some begname)) ::
    Csymbol_address (Compilenv.make_symbol ~unitname:name (Some endname)) ::
    lst
  in
  Cdata(Cglobal_symbol symbol ::
        Cdefine_symbol symbol ::
        List.fold_right addsyms namelist [cint_zero])

let data_segment_table namelist =
  segment_table namelist "caml_data_segments" "data_begin" "data_end"

let code_segment_table namelist =
  segment_table namelist "caml_code_segments" "code_begin" "code_end"

(* Initialize a predefined exception *)

let predef_exception name =
  let bucketname = "caml_bucket_" ^ name in
  let symname = "caml_exn_" ^ name in
  Cdata(Cglobal_symbol symname ::
        emit_constant symname (Const_block(0,[Const_base(Const_string name)]))
        [ Cglobal_symbol bucketname;
          Cint(block_header 0 1);
          Cdefine_symbol bucketname;
          Csymbol_address symname ])

(* Header for a plugin *)

let mapflat f l = List.flatten (List.map f l)

let plugin_header units =
  let mk (ui,crc) =
    { dynu_name = ui.ui_name;
      dynu_crc = crc;
      dynu_imports_cmi = ui.ui_imports_cmi;
      dynu_imports_cmx = ui.ui_imports_cmx;
      dynu_defines = ui.ui_defines
    } in
  global_data "caml_plugin_header"
    { dynu_magic = Config.cmxs_magic_number; dynu_units = List.map mk units }
