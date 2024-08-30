let poly_compare = compare

open Core

type un_op = 
     NOT

let string_of_un_op = function
| NOT -> "not"

type bin_op = 
   | EQ | NE | LE | LT | GE | GT
   | ADD | SUB | MUL | DIV
   | AND | OR
   | AS (* type annotation *)

let string_of_bin_op = function
| EQ -> "=="
| NE -> "!="

| LE -> "<="
| LT -> "<"
| GE -> ">="
| GT -> ">"

| ADD -> "+"
| SUB -> "-"
| MUL -> "*"
| DIV -> "//"
| AND -> "and"
| OR -> "or"
| AS -> "as"


type atom = 
   | Int of int
   | F64 of float
   | Str of string
   | Keyword of string
   | Bool of bool
   (* TODO: dependent types
   | Type of Type.ty *)

let sprintf = Core.sprintf

let append_escape acc c =
   match c with
   | '\n' -> acc ^ "\\\n"
   | '\\' -> acc ^ "\\\\"
   | c -> acc ^ (String.of_char c)

let escape str = 
   str
   |> String.to_array
   |> Array.fold ~init:"" ~f:append_escape

let string_of_atom (a: atom) = 
   match a with
   | Int i -> string_of_int i
   | F64 f -> string_of_float f
   | Str s -> sprintf {|"%s"|} (escape s)
   | Keyword k -> ":" ^ k
   | Bool true -> "True"
   | Bool false -> "False"

type ty = 
   | TInt
   | TF64
   | TStr
   | TBool
   | TKeyword
   | TTuple of ty list
   | TList of ty
   | TArrow of ty * ty (* we have currying *)

(* Random: we may extend GADT by allowing same constructor to be overloaded *)
(* https://icfp23.sigplan.org/details/ocaml-2023-papers/4/Modern-DSL-compiler-architecture-in-OCaml-our-experience-with-Catala *)

type yes = YES
type no = NO 

type exp = EXP 
type upd_pat = UPDPAT
type pat = PAT
type pat_complex = PAT_COMPLEX
type id = ID

type scope_state = Scopeful | Scopeless

type 'a exp_t = (exp, 'a) gen_ast
and 'a upd_pat_t = (upd_pat, 'a) gen_ast
and 'a pat_t = (pat, 'a) gen_ast
and 'a pat_complex_t = (pat_complex, 'a) gen_ast
and 'a id_t = (id, 'a) gen_ast
and ('ty, 'a) gen_ast = ('ty, 'a, 'a) flex_ast

(* 'd means underlaying structure, while 's means surface structure *)
and ('ty, 'd, 's) flex_ast = 

   (* Identifiers *)
   | Concrete: string -> (id, 'dep, <unique_id: no; ..> as 'sur) flex_ast 
   | Unique: string * int -> (id, 'dep, <unique_id: yes; ..> as 'sur) flex_ast 
   | Gensym: int -> (id, 'dep, 'sur) flex_ast 

   (* Updatable Patterns *)
   | Bind: 'dep id_t
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast 
   | Lens: 
   (* obj         . method      (arg1, arg2, ...) *) 
   'dep upd_pat_t * 'dep id_t * 'dep exp_t list 
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   (* PATTERN *)
   | Union: 
   (* rhs matches any of LHS, we should require LHS have same bindings and 
      corresponding bindings have same type *)
   'dep pat_t list 
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast
   
   | Updatable: 
   'dep upd_pat_t
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast
   
   | Pin: (* match with existing value *)
   'dep id_t
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PatTuple: 
   'dep pat_t list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PatList: 
   'dep pat_t list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PLit:
   atom
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | PAny:
   unit
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast

   | With:
   'dep pat_t * 'dep exp_t 
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) flex_ast


   (* Pattern Complex *)
   | PatComplex:
   'dep pat_t * 'dep pat_t list
   -> (pat_complex, 'dep, <pattern: yes; ..> as 'sur) flex_ast
      

   (* EXPRESSION *)

   (* a temporary solution, we may add algebraic effects later *)
   | Assert:
   'dep exp_t
   -> (exp, 'dep, 'sur) flex_ast

   | Val: 
   'dep id_t 
   -> (exp, 'dep, 'sur) flex_ast

   | Lit:
   atom
   -> (exp, 'dep, 'sur) flex_ast

   | Binary:
   bin_op * 'dep exp_t * 'dep exp_t
   -> (exp, 'dep, 'sur) flex_ast

   | Unary:
   un_op * 'dep exp_t
   -> (exp, 'dep, 'sur) flex_ast

   | Fix:
   'dep exp_t
   -> (exp, 'dep, 'sur) flex_ast

   | Seq:
   scope_state * 'dep exp_t list
   -> (exp, 'dep, 'sur) flex_ast

   | If:
   'dep exp_t * 'dep exp_t * 'dep exp_t
   -> (exp, 'dep, <seq: no; .. > as 'sur) flex_ast
   | IfSeq:
   'dep exp_t * 'dep exp_t list * 'dep exp_t list
   -> (exp, 'dep, <seq: yes; ..> as 'sur) flex_ast

   | Tuple: 
   'dep exp_t list
   -> (exp, 'dep, 'sur) flex_ast

   | KthTuple: 
      'dep exp_t * int 
   -> (exp, 'dep, 'sur) flex_ast

   | List: 
   'dep exp_t list
   -> (exp, 'dep, 'sur) flex_ast

   | Abs:
   'dep id_t * 'dep exp_t
   -> (exp, 'dep, <lambda: no; ..> as 'sur) flex_ast

   | Lam:
   ('dep id_t list) * 'dep exp_t
   -> (exp, 'dep, <lambda: yes; seq: no; bind_only: yes; ..> as 'sur) flex_ast
   | LamPat:
   ('dep pat_complex_t list) * 'dep exp_t
   -> (exp, 'dep, <lambda: yes; seq: no; bind_only: no; ..> as 'sur) flex_ast
   | LamPatSeq:
   ('dep pat_complex_t list) * 'dep exp_t list
   -> (exp, 'dep, <lambda: yes; seq: yes; bind_only: no; ..> as 'sur) flex_ast

   | App: 
   'dep exp_t * 'dep exp_t 
   -> (exp, 'dep, <call: no; ..> as 'sur) flex_ast

   | Call: 
   'dep id_t * 'dep exp_t list
   -> (exp, 'dep, <call: yes; ..> as 'sur) flex_ast

   | LetIn: (* we may need fix to create mutual recursive bindings here so a let may have more than one output *)
   'dep id_t * 'dep exp_t * 'dep exp_t 
   -> (exp, 'dep, <bind_only: yes; letin: yes; ..> as 'sur) flex_ast

   | BindOnly: 
   'dep id_t * 'dep exp_t
   -> (exp, 'dep, <bind_only: yes; letin: no; ..> as 'sur) flex_ast
   | BindMatch:
   'dep pat_complex_t * 'dep exp_t
   -> (exp, 'dep, <bind_only: no; ..> as 'sur) flex_ast

   | ConcreteCaseMatch: 
   (* exp to match *)
   'dep exp_t *
   (* pat  guard                 ret *)
   (atom * 'dep exp_t * 'dep exp_t) list *
   'dep exp_t option ->
   (exp, 'dep, <pattern: no; seq: no; ..> as 'sur) flex_ast

   | CaseMatch: 
   'dep exp_t *
   ('dep pat_t * 'dep exp_t * 'dep exp_t) list ->
   (exp, 'dep, <pattern: yes; seq: no; ..> as 'sur) flex_ast

   | CaseMatchSeq:
   'dep exp_t *
   ('dep pat_t * 'dep exp_t * 'dep exp_t list) list ->
   (exp, 'dep, <pattern: yes; seq: yes; ..> as 'sur) flex_ast

type top = <
   seq: yes;
   pattern: yes;
   lambda: yes;
   call: yes;
   unique_id: no;
   bind_only: no;
   letin: no>

type btm = <
   seq: no;
   pattern: no;
   lambda: no;
   call: no;
   unique_id: yes;
   bind_only: yes;
   letin: no>

type ('src, 'dst) desugarer = { f: 't. ('t, 'src) gen_ast -> ('t, 'dst) gen_ast }

let ast_compare
   (type ty src dst)
   (lhs: (ty, src, dst) flex_ast)
   (rhs: (ty, src, dst) flex_ast)
   = poly_compare lhs rhs

let shallow_map
   (type ty src dst)
   (f_wrap: (src, dst) desugarer)
   (e: (ty, src, dst) flex_ast)
   : (ty, dst) gen_ast =

   let f: 't. ('t, src) gen_ast -> ('t, dst) gen_ast = f_wrap.f in
   let f_list: 't. ('t, src) gen_ast list -> ('t, dst) gen_ast list = List.map ~f:f in

   match e with 

   (* identifier *)
   | Concrete(id) -> Concrete(id)
   | Unique(id, i) -> Unique(id, i)
   | Gensym(i) -> Gensym(i)

   (* updatable pattern *)
   | Bind(id) -> Bind(f id)
   | Lens(obj, _method, args) -> 
      Lens(f obj, f _method, f_list args )

   (* pattern *)
   | Union(alts) -> Union(f_list alts)
   | Updatable(u) -> Updatable(f u)
   | Pin(id) -> Pin(f id)
   | PatTuple(ps) -> PatTuple(f_list ps)
   | PatList(ps) -> PatList(f_list ps)
   | PLit(a) -> PLit(a)
   | PAny() -> PAny()

   (* pattern complex *)
   | PatComplex(p, ps) -> PatComplex(f p, f_list ps)

   (* expression *)
   | Val(v) -> Val(f v)
   | Lit(a) -> Lit(a)
   | Binary(op, lhs, rhs) -> Binary(op, f lhs, f rhs)
   | Unary(g, x) -> Unary(g, f x)
   | Fix(e) -> Fix(f e)
   | Seq(st, es) -> Seq(st, f_list es)
   | If(test, _then, _else) -> If(f test, f _then, f _else)
   | IfSeq(test, _then, _else) -> IfSeq(f test, f_list _then, f_list _else)
   | Tuple(es) -> Tuple(f_list es)
   | KthTuple(e, k) -> KthTuple(f e, k) 
   | List(es) -> List(f_list es)
   | Abs(id, e) -> Abs(f id, f e)
   | Lam(ids, e) -> Lam(f_list ids, f e)
   | LamPat(pats, e) -> LamPat(f_list pats, f e)
   | LamPatSeq(pats, es) -> LamPatSeq(f_list pats, f_list es)
   | App(g, x) -> App(f g, f x)
   | Call(id, es) -> Call(f id, f_list es)
   | BindMatch(lhs_patc, rhs) -> BindMatch(f lhs_patc, f rhs)
   | ConcreteCaseMatch(e, branches, _else) ->
      let f_branch (_val, guard, ret) = (_val, f guard, f ret) in 
      begin match _else with
         | Some(has_else) -> ConcreteCaseMatch(f e, List.map ~f:f_branch branches, Some(f has_else))
         | _ -> ConcreteCaseMatch(f e, List.map ~f:f_branch branches, None)
      end
   | CaseMatch(e, branches) ->
      let f_branch (pat, guard, ret) = (f pat, f guard, f ret) in
      CaseMatch(f e, List.map ~f:f_branch branches)
   | CaseMatchSeq(e, branches) ->
      let f_branch (pat, guard, ret) = (f pat, f guard, f_list ret) in
      CaseMatchSeq(f e, List.map ~f:f_branch branches)
   | LetIn(id, _val, inner) -> LetIn(f id, f _val, f inner)
   | BindOnly(id, e) -> BindOnly(f id, f e)
   | Assert(e) -> Assert(f e)
   | With(pat, e) -> With(f pat, f e)

type formatter = { f: 't. ('t, top) gen_ast -> string; }

let shallow_format
   (type ty)
   (f_wrap: formatter)
   (t: (ty, top) gen_ast)
   : string =
   let f: 't. ('t, top) gen_ast -> string = f_wrap.f in
   let f_list: 't. ('t, top) gen_ast list -> (string list -> string) -> string = 
      fun l agg -> List.map ~f:f l |> agg
   in
   match t with 

   (* identifier *)
   | Concrete id -> id
   | Gensym(i) -> sprintf "~~%d" i

   (* updatable pattern *)
   | Bind(id) -> f id
   | Lens(obj, _method, args) -> 
         sprintf "%s.%s(%s)" (f obj) (f _method) (f_list args (String.concat ~sep:","))

   (* pattern *)
   | Union(alts) -> f_list alts (String.concat ~sep:"|")
   | Updatable(u) -> f u
   | Pin(id) -> "^" ^ f id
   | PatTuple(ps) -> sprintf "(%s)" (f_list ps (String.concat ~sep:","))
   | PatList(ps) -> sprintf "[%s]" (f_list ps (String.concat ~sep:","))
   | PLit(a) -> string_of_atom a
   | PAny() -> "_"

   (* pattern complex *)
   | PatComplex(p, []) -> f p
   | PatComplex(p, ps) -> sprintf "%s=%s" (f p) (f_list ps (String.concat ~sep:"="))

   (* expression *)
   | Val(v) -> f v
   | Lit(a) -> string_of_atom a
   | Binary(op, lhs, rhs) -> sprintf "(%s %s %s)" (f lhs) (string_of_bin_op op) (f rhs)
   | Unary(g, x) -> sprintf "(%s %s)" (string_of_un_op g) (f x)
   | Fix(e) -> sprintf "fix(%s)" (f e)
   | Seq(Scopeful, es) -> sprintf "(#%s)" (f_list es (String.concat ~sep:";"))
   | Seq(Scopeless, es) -> sprintf "(%s)" (f_list es (String.concat ~sep:";"))
   | IfSeq(test, _then, _else) -> 
         sprintf 
         "if %s: %s else: %s"
         (f test)
         (f_list _then (String.concat ~sep:";"))
         (f_list _else (String.concat ~sep:";"))
   | Tuple(es) ->
         sprintf "(%s)" (f_list es (String.concat ~sep:","))
   | KthTuple _ -> "TODO"
   | List(es) -> 
         sprintf "[%s]" (f_list es (String.concat ~sep:","))
   | LamPatSeq(pats, es) -> 
         sprintf "fn(%s): %s"
         (f_list pats (String.concat ~sep:","))
         (f_list es (String.concat ~sep:";"))
   | Call(id, es) -> 
      sprintf "%s(%s)"
      (f id)
      (f_list es (String.concat ~sep:","))
   | BindMatch(lhs_patc, rhs) -> sprintf "%s=%s" (f lhs_patc) (f rhs)
   | CaseMatchSeq _ -> "TODO"
   | Assert _ -> "TODO"
   | With _ -> "TODO"

let rec ast_format: 't. ('t, 'top) gen_ast -> string = fun e ->
   shallow_format {f = ast_format} e
