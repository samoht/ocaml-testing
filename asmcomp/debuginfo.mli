(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Gallium, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2006 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

type kind =
  | Dinfo_none
  | Dinfo_call
  | Dinfo_raise
  | Dinfo_event

type t = {
  dinfo_kind: kind;
  dinfo_file: string;
  dinfo_line: int;
  dinfo_char_start: int;
  dinfo_char_end: int
}

type 'a expression = {
  exp: 'a;
  dbg: t;
}

val none: t

(** Build an expression with no debuging information (ie. with the
    value [none]) *)
val mk: 'a -> 'a expression

val mkdbg: t -> 'a -> 'a expression

(** Marshalled and unmarshalled [none] value will not be physically
    equal, so it is safer to use [is_none] instead of [(==)]. *)
val is_none : t -> bool

val string_of_dbg: t -> string

val dbg_of_location: kind -> Location.t -> t

val dbg_of_call : Lambda.lambda_event -> t
val dbg_of_raise: Lambda.lambda_event -> t
val dbg_of_event: Lambda.lambda_event -> t

val needs_slot_in_frame: t -> bool
