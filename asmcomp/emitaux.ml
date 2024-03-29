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

(* Common functions for emitting assembly code *)

open Debuginfo
open Cmm
open Reg
open Linearize

let output_channel = ref stdout

let emit_string s = output_string !output_channel s

let emit_int n = output_string !output_channel (string_of_int n)

let emit_char c = output_char !output_channel c

let emit_nativeint n = output_string !output_channel (Nativeint.to_string n)

let emit_printf fmt =
  Printf.fprintf !output_channel fmt

let emit_int32 n = emit_printf "0x%lx" n

let emit_symbol esc s =
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    match c with
      'A'..'Z' | 'a'..'z' | '0'..'9' | '_' ->
        output_char !output_channel c
    | _ ->
        Printf.fprintf !output_channel "%c%02x" esc (Char.code c)
  done

let emit_string_literal s =
  let last_was_escape = ref false in
  emit_string "\"";
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    if c >= '0' && c <= '9' then
      if !last_was_escape
      then Printf.fprintf !output_channel "\\%o" (Char.code c)
      else output_char !output_channel c
    else if c >= ' ' && c <= '~' && c <> '"' (* '"' *) && c <> '\\' then begin
      output_char !output_channel c;
      last_was_escape := false
    end else begin
      Printf.fprintf !output_channel "\\%o" (Char.code c);
      last_was_escape := true
    end
  done;
  emit_string "\""

let emit_string_directive directive s =
  let l = String.length s in
  if l = 0 then ()
  else if l < 80 then begin
    emit_string directive;
    emit_string_literal s;
    emit_char '\n'
  end else begin
    let i = ref 0 in
    while !i < l do
      let n = min (l - !i) 80 in
      emit_string directive;
      emit_string_literal (String.sub s !i n);
      emit_char '\n';
      i := !i + n
    done
  end

let emit_bytes_directive directive s =
   let pos = ref 0 in
   for i = 0 to String.length s - 1 do
     if !pos = 0
     then emit_string directive
     else emit_char ',';
     emit_int(Char.code s.[i]);
     incr pos;
     if !pos >= 16 then begin emit_char '\n'; pos := 0 end
   done;
   if !pos > 0 then emit_char '\n'

(* PR#4813: assemblers do strange things with float literals indeed,
   so we convert to IEEE representation ourselves and emit float
   literals as 32- or 64-bit integers. *)

let emit_float64_directive directive f =
  let x = Int64.bits_of_float (float_of_string f) in
  emit_printf "\t%s\t0x%Lx\n" directive x

let emit_float64_split_directive directive f =
  let x = Int64.bits_of_float (float_of_string f) in
  let lo = Int64.logand x 0xFFFF_FFFFL
  and hi = Int64.shift_right_logical x 32 in
  emit_printf "\t%s\t0x%Lx, 0x%Lx\n"
    directive
    (if Arch.big_endian then hi else lo)
    (if Arch.big_endian then lo else hi)

let emit_float32_directive directive f =
  let x = Int32.bits_of_float (float_of_string f) in
  emit_printf "\t%s\t0x%lx\n" directive x

(* Record live pointers at call points *)

type frame_descr =
  { fd_lbl: int;                        (* Return address *)
    fd_frame_size: int;                 (* Size of stack frame *)
    fd_live_offset: int list;           (* Offsets/regs of live addresses *)
    fd_debuginfo: Debuginfo.t }         (* Location, if any *)

let frame_descriptors = ref([] : frame_descr list)

type emit_frame_actions =
  { efa_label: int -> unit;
    efa_16: int -> unit;
    efa_32: int32 -> unit;
    efa_word: int -> unit;
    efa_align: int -> unit;
    efa_label_rel: int -> int32 -> unit;
    efa_def_label: int -> unit;
    efa_string: string -> unit }

let emit_frames a =
  let filenames = Hashtbl.create 7 in
  let lbl_filenames = ref 200000 in
  let label_filename name =
    try
      Hashtbl.find filenames name
    with Not_found ->
      let lbl = !lbl_filenames in
      Hashtbl.add filenames name lbl;
      incr lbl_filenames;
      lbl in
  let emit_frame fd =
    a.efa_label fd.fd_lbl;
    a.efa_16 (if Debuginfo.needs_slot_in_frame fd.fd_debuginfo
              then fd.fd_frame_size + 1
              else fd.fd_frame_size);
    a.efa_16 (List.length fd.fd_live_offset);
    List.iter a.efa_16 fd.fd_live_offset;
    a.efa_align Arch.size_addr;
    if Debuginfo.needs_slot_in_frame fd.fd_debuginfo then begin
      let d = fd.fd_debuginfo in
      let line = min 0xFFFFF d.dinfo_line
      and char_start = min 0xFF d.dinfo_char_start
      and char_end = min 0x3FF d.dinfo_char_end
      and kind = match d.dinfo_kind with
        | Dinfo_call  -> 0
        | Dinfo_raise -> 1
        | _ -> failwith "emit_frame" in
      let info =
        Int64.add (Int64.shift_left (Int64.of_int line) 44) (
        Int64.add (Int64.shift_left (Int64.of_int char_start) 36) (
        Int64.add (Int64.shift_left (Int64.of_int char_end) 26)
                  (Int64.of_int kind))) in
      a.efa_label_rel
        (label_filename d.dinfo_file)
        (Int64.to_int32 info);
      a.efa_32 (Int64.to_int32 (Int64.shift_right info 32))
    end in
  let emit_filename name lbl =
    a.efa_def_label lbl;
    a.efa_string name;
    a.efa_align Arch.size_addr in
  a.efa_word (List.length !frame_descriptors);
  List.iter emit_frame !frame_descriptors;
  Hashtbl.iter emit_filename filenames;
  frame_descriptors := []

(* Detection of functions that can be duplicated between a DLL and
   the main program (PR#4690) *)

let isprefix s1 s2 =
  String.length s1 <= String.length s2
  && String.sub s2 0 (String.length s1) = s1

let is_generic_function name =
  List.exists
    (fun p -> isprefix p name)
    ["caml_apply"; "caml_curry"; "caml_send"; "caml_tuplify"]

(* CFI directives *)

let is_cfi_enabled () =
  !Clflags.debug && Config.asm_cfi_supported

let cfi_startproc () =
  if is_cfi_enabled () then
    emit_string "	.cfi_startproc\n"

let cfi_endproc () =
  if is_cfi_enabled () then
    emit_string "	.cfi_endproc\n"

let cfi_adjust_cfa_offset n =
  if is_cfi_enabled () then
  begin
    emit_string "	.cfi_adjust_cfa_offset	"; emit_int n; emit_string "\n";
  end
 
