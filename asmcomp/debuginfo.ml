(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Gallium, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2006 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

open Lexing
open Location

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

let none = {
  dinfo_kind = Dinfo_none;
  dinfo_file = "";
  dinfo_line = 0;
  dinfo_char_start = 0;
  dinfo_char_end = 0
}

let is_none d =
  d.dinfo_kind = Dinfo_none

let to_string d =
  if d = none
  then ""
  else
    let k = match d.dinfo_kind with
      | Dinfo_none  -> "*"
      | Dinfo_call  -> "c"
      | Dinfo_raise -> "r"
      | Dinfo_event -> "e" in
    Printf.sprintf "{%s:%d,%d-%d|%s}"
           d.dinfo_file d.dinfo_line d.dinfo_char_start d.dinfo_char_end k

let check d =
  let env =
    try ignore (Sys.getenv "DBGTEST"); true
    with _ -> false in
  if env && d = none && d != none then begin
    Printexc.print_backtrace stderr;
    assert false
  end

let from_location kind loc =
  if loc == Location.none then
    none
  else
  { dinfo_kind = kind;
    dinfo_file = loc.loc_start.pos_fname;
    dinfo_line = loc.loc_start.pos_lnum;
    dinfo_char_start = loc.loc_start.pos_cnum - loc.loc_start.pos_bol;
    dinfo_char_end =
      if loc.loc_end.pos_fname = loc.loc_start.pos_fname
      then loc.loc_end.pos_cnum - loc.loc_start.pos_bol
      else loc.loc_start.pos_cnum - loc.loc_start.pos_bol }

let from kind ev =
  from_location kind ev.Lambda.lev_loc

let from_call  = from Dinfo_call 
let from_raise = from Dinfo_raise
let from_event = from Dinfo_event

let needs_frame ev = match ev.dinfo_kind with
  | Dinfo_none 
  | Dinfo_event -> false
  | Dinfo_raise
  | Dinfo_call  -> true
