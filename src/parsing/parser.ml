open Core
open Angstrom
open Ast

(* Comments *)

let space_chars : unit t =
  skip (List.mem ['\t'; ' '; '\r'; '\n'] ~equal: equal_char)

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

(* line comment doesn't consume `\n` *)
let line_comment : unit t =
  char '#' *> peek_char >>= function
    | None -> return ()
    | Some ('|') -> fail "Block comment expected"
    | _ -> skip_while (fun c -> not (equal_char c '\n'))

let white_space = many (space_chars <|> block_comment <|> line_comment)

(* Tokenizing *)

let token (tok: 'a t): 'a t =
  tok <* white_space

let tok_int = token (take_while1 (function '0' .. '9' -> true | _ -> false) >>| int_of_string)


let bin op lhs rhs = Binary(op, lhs, rhs)

let tok_as = token (string "::") *> return (bin AS)

let tok_mul = token (char '*') *> return (bin MUL)
let tok_div = token (char '/') *> return (bin DIV)

let tok_add = token (char '+') *> return (bin ADD)
let tok_sub = token (char '-') *> return (bin SUB)

let tok_eq = token (string "==") *> return (bin EQ)
let tok_ne = token (string "!=") *> return (bin NE)
let tok_le = token (string "<=") *> return (bin LE)
let tok_ge = token (string ">=") *> return (bin GE)
let tok_lt = token (string "<") *> return (bin LT)
let tok_gt = token (string ">") *> return (bin GT)

let tok_and = token (string "and") *> return (bin AND)

let tok_or = token (string "or") *> return (bin OR)

let tok_lpar = token (char '(')
let tok_rpar = token (char ')')
let tok_lbkt = token (char '[')
let tok_rbkt = token (char ']')
let tok_comma = token (char ',')
let tok_underscore = token (char '_')

let tok_with = token (string "with")
let tok_pipe = token (char '|')
let tok_dot = token (char '.')
let tok_match = token (char '=')


let tok_id = 
  let id1 = satisfy (fun c -> Char.is_alpha c || List.mem ['_'] ~equal: equal_char c) in
  let id_rest = take_while (fun c -> Char.is_alphanum c || List.mem ['_'] ~equal: equal_char c) in
  lift2 (fun id1 id_rest -> Char.to_string id1 ^ id_rest) id1 id_rest |> token

(* Parsing *)

(* Helper Functions *)

let tier_left e op =
  let rec go acc =
    (lift2 (fun f x -> f acc x) op e >>= go) <|> return acc in
  e >>= go

let wrapped_list lsep rsep sep (p: 'a t): 'a list t =
  let list_rest =
    fix (fun list_rest ->
      (rsep *> return [])
      <|> lift2 (fun x _ -> [x]) p rsep
      <|> lift3 (fun x _ xs -> x :: xs) p sep list_rest
    )
  in
  lsep *> list_rest

let sep_list sep (p: 'a t): 'a list t =
  fix (fun sep_list ->
    (p >>| fun x -> [x]) <|> lift3 (fun hd _ rest -> hd :: rest) p sep sep_list)

let atom: atom t =
  tok_int >>= (fun i -> return (Int i))

let identifier: top id_t t =
  tok_id >>| fun id -> Concrete id

let _exp_simple (pattern: top pat_t t): top exp_t t =
  fix (fun expr -> 
    let primary = 
      tok_lpar *> expr <* tok_rpar
      <|> (atom >>| fun a -> Lit a) 
      <|> (identifier >>| fun id -> Val id) 
    in
    let annonated = tier_left primary tok_as in
    let factor = tier_left annonated (tok_mul <|> tok_div) in
    let term = tier_left factor (tok_add <|> tok_sub) in 
    let predicate = tier_left term (tok_eq <|> tok_ne <|> tok_le <|> tok_ge <|> tok_lt <|> tok_gt) in 
    let pred_conjunct = tier_left predicate tok_and in 
    let pred_disjunct = tier_left pred_conjunct tok_or in 
    let match_stmt = 
      fix (fun match_stmt -> 
        (lift3 (fun pat _ exp -> BindMatch(pat, exp)) pattern tok_match match_stmt)
        <|> pred_disjunct)
    in
    match_stmt)

let _updatable_pattern (pattern: top pat_t t): top upd_pat_t t =
  let exp_simple = _exp_simple pattern in

  let arg_list = wrapped_list tok_lpar tok_rpar tok_comma exp_simple in
  let bind = identifier >>| fun b -> Bind b in
  let upd_primary = bind in
  let rec go_lens acc = 
    (lift3
     (fun _ _method args -> Lens(acc, _method, args))
     tok_dot
     identifier
     arg_list
     >>= go_lens)
    <|> return acc in
  let with_lens = upd_primary >>= go_lens in
  with_lens

let pattern: top pat_t t =
  fix (fun (pattern: top pat_t t) ->
    let updatable_pattern = _updatable_pattern pattern in
    let exp_simple = _exp_simple pattern in

    let plit = atom >>| fun a -> PLit a in
    let pany = tok_underscore *> (return (PAny ())) in
    let pupdatable = updatable_pattern >>| fun up -> Updatable up in
    let plist = wrapped_list tok_lbkt tok_rbkt tok_comma pattern >>| fun ps -> PatList ps in
    let pnest_or_tuple = wrapped_list tok_lpar tok_rpar tok_comma pattern >>| function
      | [x] -> x
      | ps -> PatTuple ps
    in
    let pprimary =
      pany
      <|> plit
      <|> plist
      <|> pnest_or_tuple
      <|> pupdatable
    in
    let withed = 
      pprimary <|> lift3 (fun pat _ cond -> With(pat, cond)) pprimary tok_with exp_simple
    in
    let unioned = sep_list tok_pipe withed >>| function 
    | [single] -> single 
    | ps -> Union ps
    in
    unioned
  )

let exp_simple = _exp_simple pattern
let updatable_pattern = _updatable_pattern pattern

let%test_module "parsing" = (module struct
  let ast_expect (type a b c) (p: (a, b, c) flex_ast t) str (ast: (a, b, c) flex_ast) =
    match parse_string ~consume:All p str with
    | Ok v ->  equal_int 0 (ast_compare v ast)
    | _ -> false

  let%test "simple expression" =
    let to_parse = "a = 1 + 3 * #|nested #|comments|# just like #|this one|#|#  4  #and also line comments" in
    let expected = BindMatch(Updatable (Bind (Concrete "a")), Binary(ADD, Lit (Int 1), Binary (MUL, Lit (Int 3), Lit (Int 4)))) in
    ast_expect exp_simple to_parse expected

  let%test "simple match" =
    let to_parse = "[1, (9, 8, c), a]" in
    let expected = PatList[PLit (Int 1); PatTuple[PLit (Int 9); PLit (Int 8); Updatable (Bind (Concrete "c"))]; Updatable (Bind (Concrete "a"))] in
    ast_expect pattern to_parse expected
end) 
