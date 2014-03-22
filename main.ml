open Lazykoq.Lazykoq ;;

(*
let result = Parser.program Lexer.token (Lexing.from_channel stdin) ;;
*)

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
      let rec loop () =
        let result = Parser.program Lexer.token lexbuf in
          print_endline (List.fold_left (fun ans ch -> (Char.escaped ch) ^ ans) "" (string_of_expr result)); print_endline "done."; flush stdout; loop ()
        in
        loop ()
     with End_of_file -> flush stdout; exit 0

