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

(* Second intermediate language (machine independent) *)

type machtype_component =
    Addr
  | Int
  | Float

type machtype = machtype_component array

val typ_void: machtype
val typ_addr: machtype
val typ_int: machtype
val typ_float: machtype

val size_component: machtype_component -> int
val size_machtype: machtype -> int

type comparison =
    Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge

val negate_comparison: comparison -> comparison
val swap_comparison: comparison -> comparison

type memory_chunk =
    Byte_unsigned
  | Byte_signed
  | Sixteen_unsigned
  | Sixteen_signed
  | Thirtytwo_unsigned
  | Thirtytwo_signed
  | Word
  | Single
  | Double                              (* 64-bit-aligned 64-bit float *)
  | Double_u                            (* word-aligned 64-bit float *)


type operation =
    Capply of machtype
  | Cextcall of string * machtype * bool
  | Cload of memory_chunk
  | Calloc
  | Cstore of memory_chunk
  | Caddi | Csubi | Cmuli | Cdivi | Cmodi
  | Cand | Cor | Cxor | Clsl | Clsr | Casr
  | Ccmpi of comparison
  | Cadda | Csuba
  | Ccmpa of comparison
  | Cnegf | Cabsf
  | Caddf | Csubf | Cmulf | Cdivf
  | Cfloatofint | Cintoffloat
  | Ccmpf of comparison
  | Craise
  | Ccheckbound


type expression_desc =
    Cconst_int of int
  | Cconst_natint of nativeint
  | Cconst_float of string
  | Cconst_symbol of string
  | Cconst_pointer of int
  | Cconst_natpointer of nativeint
  | Cvar of Ident.t
  | Clet of Ident.t * expression * expression
  | Cassign of Ident.t * expression
  | Ctuple of expression list
  | Cop of operation * expression list
  | Csequence of expression * expression
  | Cifthenelse of expression * expression * expression
  | Cswitch of expression * int array * expression array
  | Cloop of expression
  | Ccatch of int * Ident.t list * expression * expression
  | Cexit of int * expression list
  | Ctrywith of expression * Ident.t * expression

and expression = expression_desc Debuginfo.expression

type fundecl =
  { fun_name: string;
    fun_args: (Ident.t * machtype) list;
    fun_body: expression;
    fun_fast: bool }

type data_item =
    Cdefine_symbol of string
  | Cdefine_label of int
  | Cglobal_symbol of string
  | Cint8 of int
  | Cint16 of int
  | Cint32 of nativeint
  | Cint of nativeint
  | Csingle of string
  | Cdouble of string
  | Csymbol_address of string
  | Clabel_address of int
  | Cstring of string
  | Cskip of int
  | Calign of int

type phrase =
    Cfunction of fundecl
  | Cdata of data_item list
