open Core
open Angstrom
open Ast

(* Comments *)

let space_chars : unit t =
  skip (List.mem ['\t'; ' '; '\r'] ~equal: equal_char)

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

let atom_int = token (take_while1 (function '0' .. '9' -> true | _ -> false) >>| int_of_string)
let atom_true = token (string "True") *> (return true)
let atom_false = token (string "False") *> (return false)

let tok_nl = token (char '\n')
let tok_nl_star = many tok_nl
let tok_nl_plus = many1 tok_nl

let bin op lhs rhs = Binary(op, lhs, rhs)

let operator (type a) (tok: a t): a t = (token tok) <* tok_nl_star 
let roperator (type a) (tok: a t): a t =  tok_nl_star *> (token tok)

let op_as = operator (string "::") *> return (bin AS)

let op_mul = operator (char '*') *> return (bin MUL)
let op_div = operator (char '/') *> return (bin DIV)

let op_add = operator (char '+') *> return (bin ADD)
let op_sub = operator (char '-') *> return (bin SUB)

let op_eq = operator (string "==") *> return (bin EQ)
let op_ne = operator (string "!=") *> return (bin NE)
let op_le = operator (string "<=") *> return (bin LE)
let op_ge = operator (string ">=") *> return (bin GE)
let op_lt = operator (string "<") *> return (bin LT)
let op_gt = operator (string ">") *> return (bin GT)

let op_and = operator (string "and") *> return (bin AND)

let op_or = operator (string "or") *> return (bin OR)

let op_lpar = operator (char '(')
let rop_rpar = token (char ')')
let op_lbkt = operator (char '[')
let rop_rbkt = token (char ']')
let op_comma = operator (char ',')
let tok_underscore = token (char '_')

let op_with = operator (string "with")
let op_pipe = operator (char '|')
let op_dot = operator (char '.')
let tok_match = token (char '=')
let tok_if = token (string "if")
let tok_then = token (string "then")
let tok_else = token (string "else")
let tok_end = token (string "end")
let tok_colon = token (char ':')
let tok_do = token (string "do")
let tok_fn = token (string "fn")

let tok_id = 
  let id1 = satisfy (fun c -> Char.is_alpha c || List.mem ['_'] ~equal: equal_char c) in
  let id_rest = take_while (fun c -> Char.is_alphanum c || List.mem ['_'] ~equal: equal_char c) in
  lift2 (fun id1 id_rest -> Char.to_string id1 ^ id_rest) id1 id_rest |> token

(* Parsing *)

(* Helper Functions *)

let lift5 f a b c d e = (lift4 f a b c d) <*> e

let reduce_left init ele op =
  let rec go acc =
    (lift2 (fun f x -> f acc x) op ele >>= go) <|> return acc in
  init >>= go

let tier_left e op =
  reduce_left e e op

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
  atom_int >>= (fun i -> return (Int i))
  <|> ((atom_true <|> atom_false) >>= (fun b -> return (Bool b)))

let identifier: top id_t t =
  tok_id >>| fun id -> Concrete id

let _block (type a) (expression: top exp_t t) (block_terminator: a t): top exp_t list t =
  (tok_colon *> expression >>| (fun x -> [x]))
  <|> (tok_nl_plus *> (many_till (expression <* tok_nl_plus) block_terminator))

let _block_alt (type a b) (expression: top exp_t t) (block_terminator_exp: a t) (block_terminator_blk: b t): top exp_t list t =
  (tok_colon *> expression >>| (fun x -> [x])<* block_terminator_exp)
  <|> (tok_nl_plus *> (many_till (expression <* tok_nl_plus) block_terminator_blk))

let id_to_lhs (id: top id_t): top pat_t =
  Updatable(Bind(id))

let _expression (pattern: top pat_t t): top exp_t t =
  fix (fun expression -> 
    let arg_list = wrapped_list op_lpar rop_rpar op_comma expression in
    let function_call = lift2 (fun fn args -> (fn, args)) identifier arg_list in
    let primary =
      op_lpar *> expression <* rop_rpar
      <|> (function_call >>| fun (fn, args) -> Call(fn, args))
      <|> (atom >>| fun a -> Lit a)
      <|> (identifier >>| fun id -> Val id)
    in
    let ufcs = reduce_left primary function_call (op_dot *> return (fun inner (fn, args) -> Call(fn, inner :: args))) in
    let annonated = tier_left ufcs op_as in
    let factor = tier_left annonated (op_mul <|> op_div) in
    let term = tier_left factor (op_add <|> op_sub) in 
    let predicate = tier_left term (op_eq <|> op_ne <|> op_le <|> op_ge <|> op_lt <|> op_gt) in 
    let pred_conjunct = tier_left predicate op_and in 
    let pred_disjunct = tier_left pred_conjunct op_or in 
    let match_stmt = 
      fix (fun match_stmt -> 
        (lift3 (fun pat _ exp -> BindMatch(pat, exp)) pattern tok_match match_stmt)
        <|> pred_disjunct)
    in
    let expr_like = match_stmt in

    let block_alt (type a b) (term_exp: a t) (term_blk: b t) = _block_alt expression term_exp term_blk in
    let block (type a) (term: a t) = _block expression term in
    let if_stmt =
      lift4
        (fun _ cond then_clause else_clause -> IfSeq(cond, then_clause, else_clause)) 
        tok_if
        expression
        (block_alt tok_else tok_else)
        (block tok_end)
    in let do_stmt =
      lift2
      (fun _ exps -> Seq(exps))
      tok_do
      (block tok_end)
    in let params_list = wrapped_list op_lpar rop_rpar op_comma pattern
    in let lambda = 
      lift4 (fun _ id params blk -> 
        match id with
        | Some(id) -> BindMatch(Updatable(Bind(id)), LamPatSeq(params, blk))
        | None -> LamPatSeq(params, blk)
      )
      tok_fn
      (option None (identifier >>| fun x -> Some(x)))
      params_list
      (block tok_end)
    in
    do_stmt <|> if_stmt <|> lambda <|> expr_like)

let _updatable_pattern (pattern: top pat_t t): top upd_pat_t t =
  let expression = _expression pattern in

  let arg_list = wrapped_list op_lpar rop_rpar op_comma expression in
  let bind = identifier >>| fun b -> Bind b in
  let upd_primary = bind in
  let rec go_lens acc = 
    (lift3
     (fun _ _method args -> Lens(acc, _method, args))
     op_dot
     identifier
     arg_list
     >>= go_lens)
    <|> return acc in
  let with_lens = upd_primary >>= go_lens in
  with_lens

let pattern: top pat_t t =
  fix (fun (pattern: top pat_t t) ->
    let updatable_pattern = _updatable_pattern pattern in
    let expression = _expression pattern in

    let plit = atom >>| fun a -> PLit a in
    let pany = tok_underscore *> (return (PAny ())) in
    let pupdatable = updatable_pattern >>| fun up -> Updatable up in
    let plist = wrapped_list op_lbkt rop_rbkt op_comma pattern >>| fun ps -> PatList ps in
    let pnest_or_tuple = wrapped_list op_lpar rop_rpar op_comma pattern >>| function
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
      pprimary <|> lift3 (fun pat _ cond -> With(pat, cond)) pprimary op_with expression
    in
    let unioned = sep_list op_pipe withed >>| function 
    | [single] -> single 
    | ps -> Union ps
    in
    unioned
  )

let expression = _expression pattern
let updatable_pattern = _updatable_pattern pattern

let%test_module "parsing" = (module struct
  let ast_expect (type a b c) (p: (a, b, c) flex_ast t) str (ast: (a, b, c) flex_ast) =
    match parse_string ~consume:All p str with
    | Ok v ->  equal_int 0 (ast_compare v ast)
    | _ -> false

  let%test "ufcs and calls" =
    let to_parse = "g(1.add(3).mul(4).fn(9, 10),100)" in
    let expected = 
      Call(Concrete "g", [
        Call(Concrete "fn", [
          Call(Concrete "mul", [Call(Concrete "add", [Lit (Int 1); Lit (Int 3)]); Lit (Int 4)]);
          Lit (Int 9);
          Lit (Int 10)
        ]);
        Lit (Int 100)
      ])
    in
    ast_expect expression to_parse expected

  let%test "simple pattern matching" =
    let to_parse = "a = 1 + 3 * #|nested #|comments|# just like #|this one|#|#  4  #and also line comments" in
    let expected = BindMatch(Updatable (Bind (Concrete "a")), Binary(ADD, Lit (Int 1), Binary (MUL, Lit (Int 3), Lit (Int 4)))) in
    ast_expect expression to_parse expected

  let%test "simple match" =
    let to_parse = "[1, (9, 8, c), a]" in
    let expected = PatList[PLit (Int 1); PatTuple[PLit (Int 9); PLit (Int 8); Updatable (Bind (Concrete "c"))]; Updatable (Bind (Concrete "a"))] in
    ast_expect pattern to_parse expected

  let%test "simple if statement 1" =
    let to_parse = "if True: 1 else: 2" in
    let expected = IfSeq(Lit(Bool true), [Lit(Int 1)], [Lit(Int 2)]) in
    ast_expect expression to_parse expected

  let%test "simple if statement 2" =
    let to_parse = "if True: 1 else \n 2 \n end" in
    let expected = IfSeq(Lit(Bool true), [Lit(Int 1)], [Lit(Int 2)]) in
    ast_expect expression to_parse expected

  let%test "simple if statement 3" =
    let to_parse = "if True \n 1 \n else: 2" in
    let expected = IfSeq(Lit(Bool true), [Lit(Int 1)], [Lit(Int 2)]) in
    ast_expect expression to_parse expected

  let%test "simple if statement 4" =
    let to_parse = "if True \n 1 \n else \n 2 \n end" in
    let expected = IfSeq(Lit(Bool true), [Lit(Int 1)], [Lit(Int 2)]) in
    ast_expect expression to_parse expected

  let%test "do block" =
    let to_parse = "do\n 1 \n 2\n 3\n end" in
    let expected = Seq([Lit(Int 1); Lit(Int 2); Lit(Int 3)]) in
    ast_expect expression to_parse expected

  let%test "lambda" =
    let to_parse = "fn f(x): x + 1" in
    let expected = BindMatch(Updatable(Bind(Concrete("f"))), LamPatSeq([Updatable(Bind(Concrete "x"))], [Binary(ADD, Val(Concrete "x"), Lit(Int 1))])) in
    ast_expect expression to_parse expected
end) 
