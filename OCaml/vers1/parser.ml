type token =
  | ATOM of (char list)
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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
open Types

let char_list_of_string (s : string) : char list =
  List.of_seq (String.to_seq s)
# 27 "parser.ml"
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
# 20 "parser.mly"
                  ( _1 )
# 141 "parser.ml"
               : Types.item list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'item) in
    Obj.repr(
# 23 "parser.mly"
         ( [_1] )
# 148 "parser.ml"
               : 'item_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'item) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'item_list) in
    Obj.repr(
# 24 "parser.mly"
                   ( _1 :: _2 )
# 156 "parser.ml"
               : 'item_list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'formula_list) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list) in
    Obj.repr(
# 28 "parser.mly"
      ( Tseitin (_3, _8) )
# 164 "parser.ml"
               : 'item))
; (fun __caml_parser_env ->
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list) in
    Obj.repr(
# 30 "parser.mly"
      ( Assumption _5 )
# 171 "parser.ml"
               : 'item))
; (fun __caml_parser_env ->
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list) in
    Obj.repr(
# 32 "parser.mly"
      ( Rup _5 )
# 178 "parser.ml"
               : 'item))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'formula_list_nonempty) in
    Obj.repr(
# 35 "parser.mly"
                          ( _1 )
# 185 "parser.ml"
               : 'formula_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                          ( [] )
# 191 "parser.ml"
               : 'formula_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 39 "parser.mly"
            (
      let rec unwrap_not f depth =
        match f with
        | Not inner -> unwrap_not inner (depth + 1)
        | Z3Var v -> Some (depth, PosZ3Var v)
        | And lst -> Some (depth, PosAnd lst)
        | Or lst -> Some (depth, PosOr lst)
        | Imply lst -> Some (depth, PosImply lst)
        (*| _ -> None*)
      in
      match unwrap_not _1 0 with
      | Some (depth, pf) ->
          if depth mod 2 = 0 then [Pos pf] else [Neg pf]
      | None -> failwith "Unsupported formula structure in literal"
    )
# 212 "parser.ml"
               : 'formula_list_nonempty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula_list_nonempty) in
    Obj.repr(
# 54 "parser.mly"
                                        (
      let rec unwrap_not f depth =
        match f with
        | Not inner -> unwrap_not inner (depth + 1)
        | Z3Var v -> Some (depth, PosZ3Var v)
        | And lst -> Some (depth, PosAnd lst)
        | Or lst -> Some (depth, PosOr lst)
        | Imply lst -> Some (depth, PosImply lst)
        (*| _ -> None*)
      in
      let head =
        match unwrap_not _1 0 with
        | Some (depth, pf) ->
            if depth mod 2 = 0 then Pos pf else Neg pf
        | None -> failwith "Unsupported formula structure in literal"
      in
      head :: _3
    )
# 237 "parser.ml"
               : 'formula_list_nonempty))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                                ( Z3Var (char_list_of_string "True") )
# 243 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
                                ( Z3Var (char_list_of_string "False") )
# 249 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 76 "parser.mly"
                                ( Z3Var _1 )
# 256 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 77 "parser.mly"
                                ( Not _3 )
# 263 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'formula) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 78 "parser.mly"
                                                ( Imply [_3; _5] )
# 271 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list_expr) in
    Obj.repr(
# 79 "parser.mly"
                                        ( And _3 )
# 278 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'formula_list_expr) in
    Obj.repr(
# 80 "parser.mly"
                                        ( Or _3 )
# 285 "parser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 83 "parser.mly"
            ( [_1] )
# 292 "parser.ml"
               : 'formula_list_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula_list_expr) in
    Obj.repr(
# 84 "parser.mly"
                                    ( _1 :: _3 )
# 300 "parser.ml"
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
