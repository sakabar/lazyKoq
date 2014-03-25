{
  open Parser
}

let space = [' ' '\t' '\n' '\r']
let alpha = ['A'-'Z' 'a'-'z']

rule token = parse
  (* S, K, I*)
  | 'S' { S }
  | 'K' { K }
  | 'I' { I }

  (* 括弧類 *)
  | '('       { LPAREN }
  | ')'       { RPAREN }
  
  (* 制御記号 *)
  | eof       { EOF } (* { raise End_of_file } *)

  (* スペースを読み飛ばす *)
  | space+    { token lexbuf }

