open Core
open Angstrom
open Ast
open Pretty_print
open Operators

exception Unreachable

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
let atom_true = token (string "true") *> (return true)
let atom_false = token (string "false") *> (return false)
let atom_unit = token (string "()") *> (return Unit)

let tok_nl = token (char '\n')
let tok_nl_star = many tok_nl
let tok_nl_plus = many1 tok_nl

let operator (type a) (tok: a t): a t = (token tok) <* tok_nl_star 
let roperator (type a) (tok: a t): a t =  tok_nl_star *> (token tok)

let op_as = operator (string "::")

(*let op_mul = operator (char '*') *> return (bin MUL)*)
(*let op_div = operator (char '/') *> return (bin DIV)*)
(**)
(*let op_add = operator (char '+') *> return (bin ADD)*)
(*let op_sub = operator (char '-') *> return (bin SUB)*)
(**)
(*let op_eq = operator (string "==") *> return (bin EQ)*)
(*let op_ne = operator (string "!=") *> return (bin NE)*)
(*let op_le = operator (string "<=") *> return (bin LE)*)
(*let op_ge = operator (string ">=") *> return (bin GE)*)
(*let op_lt = operator (string "<") *> return (bin LT)*)
(*let op_gt = operator (string ">") *> return (bin GT)*)
(**)
(*let op_and = operator (string "and") *> return (bin AND)*)
(**)
(*let op_or = operator (string "or") *> return (bin OR)*)

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
let tok_rec = token (string "rec")
let op_semicol = operator (string ";")

let tok_forall = token (string "forall")
let tok_arrow = operator (string "->")
let tok_tcon = 
    token (string "()"
    <|> string "Int"
    <|> string "F64"
    <|> string "String"
    <|> string "Bool"
    <|> string "Keyword"
    <|> string "Char") >>| (fun s -> TCon s)

let tok_id_no_ws = 
  let id1 = satisfy (fun c -> Char.is_alpha c || List.mem ['_'] ~equal: equal_char c) in
  let id_rest = take_while (fun c -> Char.is_alphanum c || List.mem ['_'] ~equal: equal_char c) in
  lift2 (fun id1 id_rest -> Char.to_string id1 ^ id_rest) id1 id_rest

let tok_id = token tok_id_no_ws

let keyword_no_ws = char ':' *> tok_id
let keyword = token keyword_no_ws

(* Parsing *)

(* Helper Functions *)

let lift5 f a b c d e = (lift4 f a b c d) <*> e

let reduce_left init ele op =
  let rec go acc =
    (lift2 (fun f x -> f acc x) op ele >>= go) <|> return acc in
  init >>= go

let tier_left e op =
  reduce_left e e op

let tier_right e op = 
  fix (fun tier_right ->
    lift3 
    (fun lhs op rhs -> op lhs rhs)
    e
    op
    tier_right)

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
  <|> atom_unit

let identifier: top id_t t =
  tok_id >>| fun id -> Concrete id, ann_default

let _block (type a) (expression: top exp_t t) (block_terminator: a t): top exp_t list t =
  (tok_colon *> expression >>| (fun x -> [x]))
  <|> (tok_nl_plus *> (many_till (expression <* tok_nl_plus) block_terminator))

let _block_alt (type a b) (expression: top exp_t t) (block_terminator_exp: a t) (block_terminator_blk: b t): top exp_t list t =
  (tok_colon *> expression >>| (fun x -> [x])<* block_terminator_exp)
  <|> (tok_nl_plus *> (many_till (expression <* tok_nl_plus) block_terminator_blk))

let id_to_lhs (id: top id_t): top pat_t =
  Updatable(Bind(id), ann_default), ann_default

let if_stmt (expression: top exp_t t): top exp_t t =
  let block_alt (type a b) (term_exp: a t) (term_blk: b t) = _block_alt expression term_exp term_blk in
  let block (type a) (term: a t) = _block expression term in
    lift4
      (fun _ cond then_clause else_clause -> 
        If(cond, 
          (Seq(Scopeful, then_clause), ann_default), 
          (Seq(Scopeful, else_clause), ann_default)),
          ann_default) 
      tok_if
      expression
      (block_alt tok_else tok_else)
      (block tok_end)

let do_stmt (expression: top exp_t t): top exp_t t =
  let block (type a) (term: a t) = _block expression term in
    lift2
    (fun _ exps -> Seq(Scopeful, exps), ann_default)
    tok_do
    (block tok_end)

let lambda (pattern_complex: top pat_complex_t t) (expression: top exp_t t): top exp_t t =
  let block (type a) (term: a t) = _block expression term in
  let params_list = wrapped_list op_lpar rop_rpar op_comma pattern_complex in
    lift4 (fun _ id params blk -> 
      let fn = (LamPat(params, (Seq(Scopeful, blk), ann_default)), ann_default) in
      match id with
      | Some(id, _) -> 
          BindMatch(
            (PatComplex(
              (Updatable(Bind(id, ann_default), ann_default), ann_default), []), ann_default), fn), ann_default
      | None -> fn
    )
    tok_fn
    (option None (identifier >>| fun x -> Some(x)))
    params_list
    (block tok_end)

let match_stmt (pattern: top pat_t t) (expression: top exp_t t): top exp_t t =
  lift4 (fun is_rec p ps rhs -> 
    let pc = PatComplex(p, ps), ann_default in
    if is_rec then
      BindMatch(pc, (Fix((LamPat([pc], rhs), ann_default)), ann_default)), ann_default
    else 
      BindMatch(pc, rhs), ann_default)
    (option false (tok_rec *> return true))
    (pattern <* tok_match)
    (many (pattern <* tok_match))
    expression

let type_expression: yula_type t = 
  fix (fun type_expression ->
    let untiered = 
      (op_lpar *> type_expression <* op_lpar)
      <|> (((string "list(" |> token) *> type_expression <* rop_rpar) >>| fun texp -> TList texp)
      <|> (wrapped_list op_lpar rop_rpar op_comma type_expression >>| (fun texps -> TTuple texps))
      <|> lift4 (fun kw _ inner _ -> TTagged(kw, inner))
        keyword_no_ws
        (token (char '('))
        type_expression
        rop_rpar
      <|> 
      (lift4 
       (fun _ vars _ ty_exp -> 
         TForall(TypeVarSet.of_list vars, ty_exp))
       tok_forall
       (sep_list op_comma tok_id)
       tok_colon
        type_expression)
      <|> tok_tcon
      <|> (tok_id >>| (fun s -> TVar s))
    in
    let unioned = (sep_list op_pipe untiered) >>| (fun texps -> TUnion(texps)) in
    let arrowed = tier_right unioned (tok_arrow *> return (fun lhs rhs ->  TArrow(lhs, rhs))) in
    arrowed)

(*let tier_left e op =*)
(*  reduce_left e e op*)
(**)
(*let tier_right e op = *)
(*  fix (fun tier_right ->*)
(*    lift3 *)
(*    (fun lhs op rhs -> op lhs rhs)*)
(*    e*)
(*    op*)
(*    tier_right)*)

    (*let factor = tier_left annotated (op_mul <|> op_div) in*)
    (*let term = tier_left factor (op_add <|> op_sub) in *)
    (*let predicate = tier_left term (op_eq <|> op_ne <|> op_le <|> op_ge <|> op_lt <|> op_gt) in *)
    (*let pred_conjunct = tier_left predicate op_and in *)
    (*let pred_disjunct = tier_left pred_conjunct op_or in *)

let binop_tiers (inner: top exp_t t): top exp_t t =
  List.fold_left
    binops_ranked
    ~init: inner
    ~f:(fun previous_tier ops ->
      match ops with
      | [] -> raise Unreachable
      | op :: op_rest -> 
        let op_parser (op: binary_operator) = 
          (operator (string op.name))
          *> return (fun lhs rhs ->
            Call((Concrete op.name, ann_default), [lhs; rhs]), ann_default) in
        let ops_parser = List.fold_left
          op_rest
          ~init:(op_parser op)
          ~f:(fun acc ele -> acc <|> op_parser ele)
        in
        let tier = if phys_equal op.assoc Left then tier_left else tier_right in

        tier previous_tier ops_parser
    )

let _expression (pattern_complex: top pat_complex_t t) (pattern: top pat_t t): top exp_t t =
  fix (fun expression -> 
    let arg_list = wrapped_list op_lpar rop_rpar op_comma expression in
    let function_call = lift2 (fun fn args -> (fn, args)) identifier arg_list in
    let primary =
      op_lpar *> expression <* rop_rpar
      <|> (function_call >>| fun (fn, args) -> Call(fn, args), ann_default)
      <|> (atom >>| fun a -> Lit a, ann_default)
      <|> (identifier >>| fun id -> Val id, ann_default)
    in

    let ufcs = 
      reduce_left
      primary
      function_call
      (op_dot *> return (fun inner (fn, args) -> Call(fn, inner :: args), ann_default))
    in

    let maybe_annotate_postfix =
      option None (op_as *> type_expression >>| fun ty -> Some ty)
    in
    let annotated = 
      lift2 
        (fun (exp, AnnEmpty ann_original) ann_ty -> 
          exp, AnnEmpty { ann_original with ast_type = ann_ty} [@warning "-23"]
        )
        ufcs
        maybe_annotate_postfix
    in

    let tiered = binop_tiers annotated in

    (*(* TODO: refactor binary operators in to tiers *)*)
    (*let factor = tier_left annotated (op_mul <|> op_div) in*)
    (*let term = tier_left factor (op_add <|> op_sub) in *)
    (*let predicate = tier_left term (op_eq <|> op_ne <|> op_le <|> op_ge <|> op_lt <|> op_gt) in *)
    (*let pred_conjunct = tier_left predicate op_and in *)
    (*let pred_disjunct = tier_left pred_conjunct op_or in *)

    let seq_exp = lift2
      (fun head rest -> 
        match rest with
        | [] -> head
        | rest -> Seq(Scopeless, head :: rest), ann_default)
      tiered
      (many (op_semicol *> tiered)) in 
    let expr_like = seq_exp in

    (do_stmt expression)
    <|> (if_stmt expression)
    <|> (lambda pattern_complex expression)
    <|> (match_stmt pattern expression)
    <|> expr_like)

let _pattern_complex (pattern: top pat_t t): top pat_complex_t t =
  lift2 (fun p ps -> PatComplex(p, ps), ann_default) pattern (many (tok_match *> pattern)) 

let _updatable_pattern (pattern: top pat_t t): top upd_pat_t t =
  let expression = _expression (_pattern_complex pattern) pattern in

  let arg_list = wrapped_list op_lpar rop_rpar op_comma expression in
  let bind = identifier >>| fun b -> Bind b, ann_default in
  let upd_primary = bind in
  let rec go_lens acc = 
    (lift3
     (fun _ _method args -> Lens(acc, _method, args), ann_default)
     op_dot
     identifier
     arg_list
     >>= go_lens)
    <|> return acc in
  let with_lens = upd_primary >>= go_lens in
  with_lens

let pattern: top pat_t t =
  fix (fun (pattern: top pat_t t) ->
    let pattern_complex = _pattern_complex pattern in
    let updatable_pattern = _updatable_pattern pattern in
    let expression = _expression pattern_complex pattern in

    let plit = atom >>| fun a -> PLit a, ann_default in
    let pany = tok_underscore *> (return (PAny (), ann_default)) in
    let pupdatable = updatable_pattern >>| fun up -> Updatable up, ann_default in
    let plist = wrapped_list op_lbkt rop_rbkt op_comma pattern >>| fun ps -> PatList ps, ann_default in
    let pnest_or_tuple = wrapped_list op_lpar rop_rpar op_comma pattern >>| function
      | [x] -> x
      | ps -> PatTuple ps, ann_default
    in
    let pprimary =
      pany
      <|> plit
      <|> plist
      <|> pnest_or_tuple
      <|> pupdatable
    in
    let withed = 
      pprimary <|> lift3 (fun pat _ cond -> With(pat, cond), ann_default) pprimary op_with expression
    in
    let unioned = sep_list op_pipe withed >>| function 
    | [single] -> single 
    | ps -> Union ps, ann_default
    in
    unioned
  )

let expression = _expression (_pattern_complex pattern) pattern
let updatable_pattern = _updatable_pattern pattern

let p_wrap (type a) (p: a t): a t = (white_space *> tok_nl_star *> p <* tok_nl_star)

let%test_module "parsing" = (module struct
  let ast_expect (type ty) (p: (ty, top) gen_ast t) normalized to_normalize =
    match parse_string ~consume:All (p_wrap p) to_normalize with
    | Ok parsed ->
        let expect_normalized = ast_format parsed in
        (*printf "%s ?= %s\n" expect_normalized normalized; *)
        equal_string expect_normalized normalized
    | Error msg ->
        failwith msg

  let%test "ufcs and calls" =
    let to_parse = "g(1.add(3).mul(4).fn(9, 10),100)" in
    let expected = "g(fn(mul(add(1,3),4),9,10),100)" in
    ast_expect expression expected to_parse

  let%test "comments" =
    let to_parse = "a = 1 + 3 * #|nested #|comments|# just like #|this one|#|#  4  #and also line comments" in
    let expected = "a=(1 + (3 * 4))" in
    ast_expect expression expected to_parse

  let%test "rec pattern" =
    let to_parse = {|
      rec fib = fn (x)
        if x < 1
          1
        else
          fib(x - 1) + fib(x - 2)
        end
      end
    |} in
    let expected = "fib=fix(fn(fib): fn(x): (#if (x < 1): (#1) else: (#(fib((x - 1)) + fib((x - 2))))))" in
    ast_expect expression expected to_parse

  let%test "simple pattern" =
    let to_parse = "[1, (9, 8, c), a]" in
    let expected = "[1,(9,8,c),a]" in
    ast_expect pattern expected to_parse

  let%test "simple if statements" =
    let to_parses = 
      [ "if true: 1 else: 2"
      ; "if true: 1 else  \n 2 \n end" 
      ; "if true \n 1 \n else:2" 
      ; "if true \n 1 \n else  \n 2 \n end" 
      ] in
    let expected = "if true: (#1) else: (#2)" in
    List.for_all to_parses ~f:(ast_expect expression expected)

  let%test "scopeful block" =
    let to_parse = "do\n 1 \n 2\n 3\n end" in
    let expected = "(#1;2;3)" in
    ast_expect expression expected to_parse

  let%test "scopeless sequence" =
    let to_parse = "1; 2; 3" in
    let expected = "(1;2;3)" in
    ast_expect expression expected to_parse

  let%test "simple lambdas" =
    let to_parses = 
      [ "fn f(x)\nx+1\nend"
      ; "fn f(x): x + 1" 
      ] in
    let expected = "f=fn(x): (#(x + 1))" in
    List.for_all to_parses ~f:(ast_expect expression expected)

end) 
