(* ========================================================================= *)
(* Find ML definitions in HOL Light sources.                                 *)
(* (Very crude and simplistic, yet sufficiently useful.)                     *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi, Cosimo Perini Brogi 2026 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Compilation:                                                              *)
(*   ocamlc -I +str str.cma -o finddefs finddefs.ml                          *)
(* Usage:                                                                    *)
(*   find *.ml -type f -print0 | xargs -n1 -0 finddefs > DEFS.tex            *)
(* ------------------------------------------------------------------------- *)

let let_re = Str.regexp "^let[ \t]+\\([A-Za-z0-9_']+\\)"
let end_re = Str.regexp ".*;;[ \t\r]*$"

let extract_id line =
  if Str.string_match let_re line 0 then
    Some (Str.matched_group 1 line)
  else
    None

let find_defs file =
  let ic = open_in file in

  let rec loop line_no current acc =
    match input_line ic with
    | exception End_of_file ->
        close_in ic;
        List.rev acc

    | line ->
        let line_no = line_no + 1 in

        let current, acc =
          match current with
          | None ->
              begin match extract_id line with
              | None ->
                  None, acc

              | Some id ->
                  if Str.string_match end_re line 0 then
                    None, (id, line_no, line_no) :: acc
                  else
                    Some (id, line_no), acc
              end

          | Some (id, start_line) ->
              if Str.string_match end_re line 0 then
                None, (id, start_line, line_no) :: acc
              else
                current, acc
        in

        loop line_no current acc
  in
  loop 0 None []

let () =
  if Array.length Sys.argv <> 2 then begin
    Printf.eprintf "Uso: %s file.ml\n" Sys.argv.(0);
    exit 1
  end;

  let path = Sys.argv.(1) in
  find_defs path
  |> List.iter (fun (id, i, j) ->
       Printf.printf "\\srccode{%s}{%s}{%d}{%d}\n" id path i j)