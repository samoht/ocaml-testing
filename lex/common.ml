(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Luc Maranget, projet Moscova,                            *)
(*                         INRIA Rocquencourt                          *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

open Printf
open Syntax
open Lexgen


(* To copy the ML code fragments *)

let copy_buffer = String.create 1024

let copy_chars_unix ic oc start stop =
  let n = ref (stop - start) in
  while !n > 0 do
    let m = input ic copy_buffer 0 (min !n 1024) in
    output oc copy_buffer 0 m;
    n := !n - m
  done

let copy_chars_win32 ic oc start stop =
  for i = start to stop - 1 do
    let c = input_char ic in
    if c <> '\r' then output_char oc c
  done

let copy_chars =
  match Sys.os_type with
    "Win32" | "Cygwin" -> copy_chars_win32
  | _       -> copy_chars_unix

let copy_chunk sourcefile ic oc loc =
  if loc.start_pos < loc.end_pos then begin
    fprintf oc "# %d \"%s\"\n" loc.start_line sourcefile;
    for i = 1 to loc.start_col do output_char oc ' ' done;
    seek_in ic loc.start_pos;
    copy_chars ic oc loc.start_pos loc.end_pos
  end

(* Various memory actions *)

let output_mem_access oc i = fprintf oc "lexbuf.Lexing.lex_mem.(%d)" i

let output_memory_actions pref oc = function
  | []  -> ()
  | mvs ->
      output_string oc "(* " ;
  fprintf oc "L=%d " (List.length mvs) ;
  List.iter
    (fun mv -> match mv with
    | Copy (tgt, src) ->
        fprintf oc "[%d] <- [%d] ;" tgt src
    | Set tgt ->
        fprintf oc "[%d] <- p ; " tgt)
    mvs ;
  output_string oc " *)\n" ;
  List.iter
    (fun mv -> match mv with
    | Copy (tgt, src) ->
        fprintf oc
          "%s%a <- %a ;\n"
          pref output_mem_access tgt output_mem_access src
    | Set tgt ->
        fprintf oc "%s%a <- lexbuf.Lexing.lex_curr_pos ;\n"
          pref output_mem_access tgt)
    mvs

let output_base_mem oc = function
  | Mem i -> output_mem_access oc i
  | Start -> fprintf oc "lexbuf.Lexing.lex_start_pos"
  | End   -> fprintf oc  "lexbuf.Lexing.lex_curr_pos"

let output_tag_access oc = function
  | Sum (a,0) ->
      output_base_mem oc a
  | Sum (a,i) ->
      fprintf oc "(%a + %d)" output_base_mem a i

let output_env oc env =
  let pref = ref "let" in
  match env with
  | [] -> ()
  | _  -> 
      List.iter
        (fun (x,v) ->
          begin match v with
          | Ident_string (o,nstart,nend) ->
              fprintf oc
                "\n  %s %s = Lexing.sub_lexeme%s lexbuf %a %a"
                !pref x (if o then "_opt" else "")
                output_tag_access nstart output_tag_access nend
          | Ident_char (o,nstart) ->
              fprintf oc
                "\n  %s %s = Lexing.sub_lexeme_char%s lexbuf %a"
                !pref x (if o then "_opt" else "")
                output_tag_access nstart
          end ;
          pref := "and")
        env ;
      fprintf oc " in\n"