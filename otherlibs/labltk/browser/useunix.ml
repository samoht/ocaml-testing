(*************************************************************************)
(*                                                                       *)
(*                Objective Caml LablTk library                          *)
(*                                                                       *)
(*            Jacques Garrigue, Kyoto University RIMS                    *)
(*                                                                       *)
(*   Copyright 1999 Institut National de Recherche en Informatique et    *)
(*   en Automatique and Kyoto University.  All rights reserved.          *)
(*   This file is distributed under the terms of the GNU Library         *)
(*   General Public License.                                             *)
(*                                                                       *)
(*************************************************************************)

(* $Id$ *)

open Unix

let get_files_in_directory dir =
  match
    try Some(opendir dir) with Unix_error _ -> None
  with
    None -> []
  | Some dirh ->
      let rec get_them l =
        match
          try Some(readdir dirh) with _ -> None
        with
        | Some x ->
            get_them (x::l)
        | None ->
            closedir dirh; l 
      in
      Sort.list order:(<=) (get_them [])

let is_directory name =
  try
    (stat name).st_kind = S_DIR
  with _ -> false

let get_directories_in_files :path =
  List.filter f:(fun x -> is_directory  (path ^ "/" ^ x))

(************************************************** Subshell call *)
let subshell :cmd =
  let rc = open_process_in cmd in
  let rec it l =
    match
      try Some(input_line rc) with _ -> None
    with
      Some x -> it (x::l)
    | None -> List.rev l
  in 
  let answer = it [] in
  ignore (close_process_in rc);
  answer
