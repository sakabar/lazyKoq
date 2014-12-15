open Lazykoq;;

let rec range n m = if n == m then [n] else n::(range (n+1) m);;

let charList_of_string str = List.map (fun n -> str.[n]) (range 0 ((String.length str) - 1));;

let string_of_charList chLst = (List.fold_left (fun ans ch -> (Char.escaped ch) ^ ans) "" (List.rev chLst))

let string_of_expr lmd =
  let chLst = (Lz.charList_of_expr lmd) in
    string_of_charList chLst ;;

let input_expr =
  let input_string = input_line stdin in
    Lz.expr_of_string (charList_of_string input_string) ;;

let result_string src_expr =
  let result_expr = (Lz.getOpt (Lz.eval (Lz.A (src_expr, input_expr))) (Lz.i)) in
    (Lz.string_of_churchStream result_expr);;

let _ =
  (* argv.(0) はプログラム名 *)
  let lazySrc = if (Array.length Sys.argv) > 1 then Sys.argv.(1) else "./sample/echo.lazy" in
  let srcChannel = open_in lazySrc in
  let src_expr =
    try
      let lexbuf = Lexing.from_channel srcChannel in
        Parser.program Lexer.token lexbuf
    with
      Parsing.Parse_error -> Lz.i
  in
    close_in srcChannel;
    print_endline (string_of_charList (result_string src_expr));;
