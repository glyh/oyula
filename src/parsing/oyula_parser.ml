open Core
open Angstrom
open Ast

(* Tokenizing *)

let space_chars : unit t =
  skip (List.mem ['\t'; ' '] ~equal: equal_char)

type line_comment_case =
  | Short
  | NotLineComment
  | Yes

(* line comment doesn't consume the newline token *)
let line_comment : unit t =
  char '#' *> peek_char >>= function
    | None -> return ()
    | Some ('|') -> fail "Block comment expected"
    | _ -> skip_while (fun c -> not (equal_char c '\n'))
  
let block_comment: unit t =
  let non_nested: unit t = 
    satisfy (fun c -> not (List.mem ['#'; '|'] c ~equal: equal_char)) *> (return ())
    <|> 
    (let+ _ = char '#'
     and+ _ = satisfy (fun c -> not (equal_char c '|')) in
     ())
    <|> 
    (let+ _ = char '|'
     and+ _ = satisfy (fun c -> not (equal_char c '#')) in
     ())
 in
  fix (fun (block_comment: unit t) ->
    let+ _ = string "#|"
    and+_ = many (non_nested <|> block_comment) *> (return ())
    and+ _ = string "|#" in
    ())

let white_space = many (space_chars <|> line_comment <|> block_comment)

let token (tok: 'a t): 'a t =
  tok <* white_space

let integer = token (take_while1 (function '0' .. '9' -> true | _ -> false) >>| int_of_string)

let tok_as = token (string "::") *> return AS

let tok_mul = token (char '*') *> return MUL
let tok_div = token (char '/') *> return DIV

let ops_mul = tok_mul <|> tok_div

let tok_add = token (char '+') *> return ADD
let tok_sub = token (char '-') *> return SUB

let ops_add = tok_add <|> tok_sub

let tok_eq = token (string "==") *> return EQ
let tok_ne = token (string "!=") *> return NE
let tok_le = token (string "<=") *> return LE
let tok_ge = token (string ">=") *> return GE
let tok_lt = token (string "<") *> return LT
let tok_gt = token (string ">") *> return GT

let ops_rel = tok_eq <|> tok_ne <|> tok_le <|> tok_ge <|> tok_lt <|> tok_gt

let tok_and = token (string "and") *> return OR

let tok_or = token (string "or") *> return OR

(* Parsing *)

let chainl1 e op =
  let rec go acc =
    (lift2 (fun f x -> Binary(f, acc, x)) op e >>= go) <|> return acc in
  e >>= fun init -> go init

let parens p = char '(' *> p <* char ')'

type expr = top exp_t

let exp_atom: expr t =
  integer >>= (fun i -> return (Lit(Int i)))

let exp_simple: expr t =
  fix (fun expr -> 
    let primary = parens expr <|> exp_atom in
    let annonated = chainl1 primary tok_as in
    let factor = chainl1 annonated ops_mul in
    let term = chainl1 factor ops_add in 
    let predicate = chainl1 term ops_rel in 
    let pred_conjunct = chainl1 predicate tok_and in 
    let pred_disjunct = chainl1 pred_conjunct tok_or in 
    pred_disjunct)

let%test_module "parsing" = (module struct
  let ast_expect str ast =
    match parse_string ~consume:All exp_simple str with
    | Ok v ->  equal_int 0 (ast_compare v ast)
    | _ -> false

  let%test "simple expression" =
    let to_parse = "1 + 3 * #|nested #|comments|# just like #|this one|#|#  4  #and also line comments" in
    let expected = (Binary(ADD, Lit (Int 1), Binary (MUL, Lit (Int 3), Lit (Int 4)))) in
    ast_expect to_parse expected
end) 
