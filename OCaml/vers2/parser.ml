type token =
  | ATOM of (
# 33 "parser.mly"
        char list
# 6 "parser.ml"
)
  | TRUE
  | FALSE
  | NOT
  | IMPLIES
  | AND
  | OR
  | TSEITIN
  | ASSUMPTION
  | RUP
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | COMMA
  | EOF

open Parsing
let _ = parse_error;;
# 2 "parser.mly"
open Proven_sat_checker
open Types

let char_list_of_string (s : string) : char list =
  List.of_seq (String.to_seq s)

let rec to_listZ3_Formula (lst : z3_Formula list) : listZ3_Formula =
  match lst with
  | [] -> Lnil
  | x :: xs -> Lcons (x, to_listZ3_Formula xs)

let rec normalize f =
  match f with
  | Not inner ->
      begin match normalize inner with
      | Not inner2 -> normalize inner2  (* remove double negation *)
      | simplified -> Not simplified
      end
  | And lst -> And (normalize_list lst)
  | Or lst -> Or (normalize_list lst)
  | Imply (a, b) -> Imply (normalize a, normalize b)
  | Z3var _ -> f

and normalize_list lst =
  match lst with
  | Lnil -> Lnil
  | Lcons (x, xs) -> Lcons (normalize x, normalize_list xs)

let item_counter = ref 0
# 56 "parser.ml"
let yytransl_const = [|
  258 (* TRUE *);
  259 (* FALSE *);
  260 (* NOT *);
  261 (* IMPLIES *);
  262 (* AND *);
  263 (* OR *);
  264 (* TSEITIN *);
  265 (* ASSUMPTION *);
  266 (* RUP *);
  267 (* LPAREN *);
  268 (* RPAREN *);
  269 (* LBRACK *);
  270 (* RBRACK *);
  271 (* COMMA *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* ATOM *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\003\000\003\000\004\000\004\000\
\005\000\005\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\007\000\007\000\000\000"

let yylen = "\002\000\
\002\000\001\000\002\000\009\000\006\000\006\000\001\000\000\000\
\001\000\003\000\001\000\001\000\001\000\004\000\006\000\004\000\
\004\000\001\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\020\000\000\000\000\000\
\000\000\000\000\000\000\001\000\003\000\013\000\011\000\012\000\
\000\000\000\000\000\000\000\000\000\000\007\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\010\000\
\000\000\000\000\014\000\000\000\000\000\016\000\017\000\000\000\
\005\000\006\000\000\000\019\000\000\000\015\000\000\000\004\000"

let yydgoto = "\002\000\
\006\000\007\000\008\000\021\000\022\000\023\000\037\000"

let yysindex = "\002\000\
\016\255\000\000\005\255\006\255\014\255\000\000\020\000\016\255\
\007\255\015\255\017\255\000\000\000\000\000\000\000\000\000\000\
\019\255\021\255\022\255\023\255\024\255\000\000\013\255\025\255\
\026\255\007\255\007\255\007\255\007\255\027\255\007\255\007\255\
\007\255\029\255\020\255\028\255\030\255\032\255\031\255\000\000\
\033\255\034\255\000\000\007\255\007\255\000\000\000\000\036\255\
\000\000\000\000\038\255\000\000\007\255\000\000\037\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\037\000\
\040\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\003\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\039\255\
\039\255\000\000\000\000\042\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\039\255\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\038\000\000\000\224\255\024\000\234\255\229\255"

let yytablesize = 55
let yytable = "\041\000\
\042\000\038\000\001\000\034\000\035\000\036\000\036\000\014\000\
\015\000\016\000\017\000\018\000\019\000\020\000\009\000\009\000\
\009\000\052\000\010\000\012\000\055\000\051\000\036\000\003\000\
\004\000\005\000\011\000\031\000\024\000\026\000\025\000\027\000\
\028\000\029\000\044\000\030\000\002\000\032\000\033\000\039\000\
\043\000\046\000\045\000\047\000\048\000\013\000\049\000\050\000\
\053\000\054\000\056\000\008\000\008\000\018\000\040\000"

let yycheck = "\032\000\
\033\000\029\000\001\000\026\000\027\000\028\000\029\000\001\001\
\002\001\003\001\004\001\005\001\006\001\007\001\012\001\011\001\
\014\001\045\000\013\001\000\000\053\000\044\000\045\000\008\001\
\009\001\010\001\013\001\015\001\014\001\011\001\014\001\011\001\
\011\001\011\001\015\001\012\001\000\000\013\001\013\001\013\001\
\012\001\012\001\015\001\012\001\014\001\008\000\014\001\014\001\
\013\001\012\001\014\001\012\001\014\001\012\001\031\000"

let yynames_const = "\
  TRUE\000\
  FALSE\000\
  NOT\000\
  IMPLIES\000\
  AND\000\
  OR\000\
  TSEITIN\000\
  ASSUMPTION\000\
  RUP\000\
  LPAREN\000\
  RPAREN\000\
  LBRACK\000\
  RBRACK\000\
  COMMA\000\
  EOF\000\
  "

let yynames_block = "\
  ATOM\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'item_list) in
    Obj.repr(
# 45 "parser.mly"
                  ( _1 )
# 170 "parser.ml"
               : Types.item list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'item) in
    Obj.repr(
# 54 "parser.mly"
         (
      incr item_counter;
      if !item_counter mod 10000 = 0 then
        Printf.printf "Parsed %d items\n%!" !item_counter;
      [_1]
    )
# 182 "parser.ml"
               : 'item_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'item) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'item_list) in
    Obj.repr(
# 60 "parser.mly"
                   (
      incr item_counter;
      if !item_counter mod 10000 = 0 then
        Printf.printf "Parsed %d items\n%!" !item_counter;
      _1 :: _2
    )
# 195 "parser.ml"
               : 'item_list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'formula_list) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list) in
    Obj.repr(
# 69 "parser.mly"
      ( Tseitin (_3, _8) )
# 203 "parser.ml"
               : 'item))
; (fun __caml_parser_env ->
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list) in
    Obj.repr(
# 71 "parser.mly"
      ( Assumption _5 )
# 210 "parser.ml"
               : 'item))
; (fun __caml_parser_env ->
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list) in
    Obj.repr(
# 73 "parser.mly"
      ( Rup _5 )
# 217 "parser.ml"
               : 'item))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'formula_list_nonempty) in
    Obj.repr(
# 76 "parser.mly"
                          ( _1 )
# 224 "parser.ml"
               : 'formula_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "parser.mly"
                          ( Lnil )
# 230 "parser.ml"
               : 'formula_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 80 "parser.mly"
            (
      let simplified = normalize _1 in
      Lcons (simplified, Lnil)
    )
# 240 "parser.ml"
               : 'formula_list_nonempty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula_list_nonempty) in
    Obj.repr(
# 85 "parser.mly"
                                        (
      let simplified = normalize _1 in
      Lcons (simplified, _3)
    )
# 251 "parser.ml"
               : 'formula_list_nonempty))
; (fun __caml_parser_env ->
    Obj.repr(
# 130 "parser.mly"
                                ( Z3var (char_list_of_string "True") )
# 257 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    Obj.repr(
# 131 "parser.mly"
                                ( Z3var (char_list_of_string "False") )
# 263 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 132 "parser.mly"
                                ( Z3var _1 )
# 270 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 133 "parser.mly"
                                ( Not _3 )
# 277 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'formula) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 134 "parser.mly"
                                                ( Imply (_3, _5) )
# 285 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list_expr) in
    Obj.repr(
# 135 "parser.mly"
                                        ( And _3 )
# 292 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list_expr) in
    Obj.repr(
# 136 "parser.mly"
                                        ( Or _3 )
# 299 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 139 "parser.mly"
            ( Lcons (_1, Lnil) )
# 306 "parser.ml"
               : 'formula_list_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula_list_expr) in
    Obj.repr(
# 140 "parser.mly"
                                    ( Lcons (_1, _3) )
# 314 "parser.ml"
               : 'formula_list_expr))
(* Entry start *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let start (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Types.item list)
