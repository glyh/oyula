(* Types *)

module Base_Map = Map

type tvar = top id_t
let equal_tvar lhs rhs =
   raise Unimplemented

module TypeVarSet = Set.Make(struct
   type t = tvar
   let compare = compare
end) 

type type_var_set = TypeVarSet.t

let equal_type_var_set = TypeVarSet.equal

type yula_type = 
   | TForall of type_var_set * yula_type
   | TVar of tvar

   | TArrow of yula_type * yula_type
   | TList of yula_type
   | TTuple of yula_type list

   | TUnion of yula_type list
   | TTagged of string * yula_type

   | TCon of string (* Unit, Int, Bool, Char, etc. *)
   [@@deriving eq]

let t_unit = TCon "()"
let t_int = TCon "Int"
let t_f64 = TCon "F64"
let t_string = TCon "String"
let t_bool = TCon "Bool"
let t_keyword = TCon "Keyword"
let t_char = TCon "Char"

let gen_tvar: unit -> tvar =
  let uid = ref 0 in
  fun () -> 
    uid := !uid + 1;
    Printf.sprintf "__gen_%d" !uid

let pretty_print_var_set (s: type_var_set) =
  s
  |> TypeVarSet.to_seq
  |> List.of_seq
  |> String.concat ","

let rec pretty_print_type (v: yula_type) =
  match v with
  | TForall(vars, inner) -> 
      Printf.sprintf
      "forall %s: %s"
        (pretty_print_var_set vars)
        (pretty_print_type inner)
  | TVar v -> v
  | TArrow(TArrow _ as lhs, rhs) ->
      Printf.sprintf "(%s) -> %s" (pretty_print_type lhs) (pretty_print_type rhs) 
  | TArrow(lhs, rhs) -> 
      Printf.sprintf "%s -> %s" (pretty_print_type lhs) (pretty_print_type rhs) 
  | TList(inner) -> Printf.sprintf "list(%s)" (pretty_print_type inner)
  | TTuple(tys) -> Printf.sprintf "(%s)" (List.map pretty_print_type tys |> String.concat " ")
  | TUnion(tys) -> (List.map pretty_print_type tys |> String.concat " | ")
  | TTagged(tag, ty) -> Printf.sprintf ":%s(%s)" tag (pretty_print_type ty)
  | TCon ty -> ty


(* Ast *)
let poly_compare = compare

open Core

exception Unimplemented

type un_op = 
     NOT

let string_of_un_op = function
| NOT -> "not"

type bin_op = 
   | EQ | NE | LE | LT | GE | GT
   | ADD | SUB | MUL | DIV
   | AND | OR

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


type atom = 
   | Int of int
   | F64 of float
   | Str of string
   | Char of char
   | Keyword of string
   | Bool of bool
   | Unit
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
   | Unit -> "()"
   | Char c -> sprintf {|'%s'|} (append_escape "" c)

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
and ('ty, 'a) naked_gen_ast = ('ty, 'a, 'a) naked_flex_ast
and ('ty, 'd, 's) flex_ast = ('ty, 'd, 's) naked_flex_ast * ('ty, 's) annotation

and ('ty, 'feat) annotation =
   | AnnEmpty: unit -> ('ty, <typed: no; ..> as 'feat) annotation
   | AnnTyped: {ast_type: yula_type option} -> ('ty, <typed: yes; ..> as 'feat) annotation

(* 'd means underlaying structure, while 's means surface structure *)
and ('ty, 'd, 's) naked_flex_ast = 

   (* Identifiers *)
   | Concrete: string -> (id, 'dep, 'sur) naked_flex_ast 
   | Gensym: int -> (id, 'dep, 'sur) naked_flex_ast 

   (* Updatable Patterns *)
   | Bind: 'dep id_t
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast 
   | Lens: 
   (* obj         . method      (arg1, arg2, ...) *) 
   'dep upd_pat_t * 'dep id_t * 'dep exp_t list 
   -> (upd_pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

   (* PATTERN *)
   | Union: 
   (* rhs matches any of LHS, we should require LHS have same bindings and 
      corresponding bindings have same type *)
   'dep pat_t list 
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast
   
   | Updatable: 
   'dep upd_pat_t
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast
   
   | Pin: (* match with existing value *)
   'dep id_t
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

   | PatTuple: 
   'dep pat_t list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

   | PatList: 
   'dep pat_t list
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

   | PLit:
   atom
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

   | PAny:
   unit
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

   | With:
   'dep pat_t * 'dep exp_t 
   -> (pat, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast


   (* Pattern Complex *)
   | PatComplex:
   'dep pat_t * 'dep pat_t list
   -> (pat_complex, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast
      

   (* EXPRESSION *)

   | TypeAnnotated:
      'dep exp_t * yula_type
      -> (exp, 'dep, <typed: no; ..> as 'sur) naked_flex_ast

   (* NOTE: a temporary solution, we may add algebraic effects later *)
   | Assert:
   'dep exp_t
   -> (exp, 'dep, 'sur) naked_flex_ast

   | Val: 
   'dep id_t 
   -> (exp, 'dep, 'sur) naked_flex_ast

   | Lit:
   atom
   -> (exp, 'dep, 'sur) naked_flex_ast

   | Binary:
   bin_op * 'dep exp_t * 'dep exp_t
   -> (exp, 'dep, 'sur) naked_flex_ast

   | Unary:
   un_op * 'dep exp_t
   -> (exp, 'dep, 'sur) naked_flex_ast

   | Fix:
   'dep exp_t
   -> (exp, 'dep, 'sur) naked_flex_ast

   | SeqScope:
   'dep exp_t list
   -> (exp, 'dep, <letin: no; scoped_seq: yes; ..> as 'sur) naked_flex_ast

   | Seq:
   scope_state * 'dep exp_t list
   -> (exp, 'dep, <letin: no; scoped_seq: no; ..> as 'sur) naked_flex_ast

   | If:
   'dep exp_t * 'dep exp_t * 'dep exp_t
   -> (exp, 'dep, 'sur) naked_flex_ast

   | Tuple: 
   'dep exp_t list
   -> (exp, 'dep, 'sur) naked_flex_ast

   | KthTuple: 
      'dep exp_t * int 
   -> (exp, 'dep, 'sur) naked_flex_ast

   | List: 
   'dep exp_t list
   -> (exp, 'dep, 'sur) naked_flex_ast

   | Abs:
   'dep id_t * 'dep exp_t
   -> (exp, 'dep, <currying: yes; ..> as 'sur) naked_flex_ast

   | AbsU: (* arg being of unit type *)
   'dep exp_t
   -> (exp, 'dep, <currying: yes; ..> as 'sur) naked_flex_ast

   | Lam:
   ('dep id_t list) * 'dep exp_t
   -> (exp, 'dep, <currying: no; pattern: no; ..> as 'sur) naked_flex_ast
   | LamPat:
   ('dep pat_complex_t list) * 'dep exp_t
   -> (exp, 'dep, <currying: no; pattern: yes; ..> as 'sur) naked_flex_ast

   | App: 
   'dep exp_t * 'dep exp_t 
   -> (exp, 'dep, <currying: yes; ..> as 'sur) naked_flex_ast

   | Call: 
   'dep id_t * 'dep exp_t list
   -> (exp, 'dep, <currying: no; ..> as 'sur) naked_flex_ast

   | LetIn: (* we may need fix to create mutual recursive bindings here so a let may have more than one output *)
   'dep id_t * 'dep exp_t * 'dep exp_t 
   -> (exp, 'dep, <pattern: no; letin: yes; ..> as 'sur) naked_flex_ast

   | BindOnly: 
   'dep id_t * 'dep exp_t
   -> (exp, 'dep, <pattern: no; letin: no; ..> as 'sur) naked_flex_ast
   | BindMatch:
   'dep pat_complex_t * 'dep exp_t
   -> (exp, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

   | ConcreteCaseMatch: 
   (* exp to match *)
   'dep exp_t *
   (* pat  guard                 ret *)
   (atom * 'dep exp_t * 'dep exp_t) list *
   'dep exp_t option ->
   (exp, 'dep, <pattern: no; ..> as 'sur) naked_flex_ast

   | CaseMatch: 
   'dep exp_t *
   ('dep pat_t * 'dep exp_t * 'dep exp_t) list ->
   (exp, 'dep, <pattern: yes; ..> as 'sur) naked_flex_ast

(* Default Annotations *)
type top = <
   typed: no;
   pattern: yes;
   currying: no;
   scoped_seq: no;
   letin: no>

type btm = <
   typed: yes;
   pattern: no;
   currying: yes;
   scoped_seq: yes;
   letin: no>

module TypeEnv = Base_Map.Make(struct 
  type t = top id_t
  let compare = poly_compare
end)

type type_env = yula_type TypeEnv.t


type ('src, 'dst) desugarer = { f: 't. ('t, 'src) gen_ast -> ('t, 'dst) gen_ast }

let ast_compare
   (type ty src dst)
   (lhs: (ty, src, dst) flex_ast)
   (rhs: (ty, src, dst) flex_ast)
   = poly_compare lhs rhs

let shallow_map_naked
   (type ty src dst)
   (f_wrap: (src, dst) desugarer)
   (e: (ty, src, dst) naked_flex_ast)
   : (ty, dst) naked_gen_ast =

   let f: 't. ('t, src) gen_ast -> ('t, dst) gen_ast = f_wrap.f in
   let f_list: 't. ('t, src) gen_ast list -> ('t, dst) gen_ast list = List.map ~f:f in

   match e with 

   (* identifier *)
   | Concrete(id) -> Concrete(id)
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
   | Tuple(es) -> Tuple(f_list es)
   | KthTuple(e, k) -> KthTuple(f e, k) 
   | List(es) -> List(f_list es)
   | Abs(id, e) -> Abs(f id, f e)
   | AbsU(e) -> AbsU(f e)
   | Lam(ids, e) -> Lam(f_list ids, f e)
   | LamPat(pats, e) -> LamPat(f_list pats, f e)
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
   | LetIn(id, _val, inner) -> LetIn(f id, f _val, f inner)
   | BindOnly(id, e) -> BindOnly(f id, f e)
   | Assert(e) -> Assert(f e)
   | With(pat, e) -> With(f pat, f e)
   | SeqScope(es) -> SeqScope(f_list es)
   | TypeAnnotated(exp, ty) -> TypeAnnotated(f exp, ty)

let shallow_map
   (type ty src dst)
   (f_wrap: (src, dst) desugarer)
   (e: (ty, src, dst) flex_ast)
   : (ty, dst) gen_ast =
      let (naked, ann) = e in
      shallow_map_naked f_wrap naked, ann 

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
   | Concrete id, _ -> id
   | Gensym i, _ -> sprintf "~~%d" i

   (* updatable pattern *)
   | Bind id, _ -> f id
   | Lens(obj, _method, args), _ -> 
         sprintf "%s.%s(%s)" (f obj) (f _method) (f_list args (String.concat ~sep:","))

   (* pattern *)
   | Union alts, _ -> f_list alts (String.concat ~sep:"|")
   | Updatable u, _ -> f u
   | Pin id, _ -> "^" ^ f id
   | PatTuple ps, _ -> sprintf "(%s)" (f_list ps (String.concat ~sep:","))
   | PatList ps, _ -> sprintf "[%s]" (f_list ps (String.concat ~sep:","))
   | PLit a, _ -> string_of_atom a
   | PAny (), _ -> "_"

   (* pattern complex *)
   | PatComplex(p, []), _ -> f p
   | PatComplex(p, ps), _ -> sprintf "%s=%s" (f p) (f_list ps (String.concat ~sep:"="))

   (* expression *)
   | Val(v), _ -> f v
   | Lit(a), _ -> string_of_atom a
   | Binary(op, lhs, rhs), _ -> sprintf "(%s %s %s)" (f lhs) (string_of_bin_op op) (f rhs)
   | Unary(g, x), _ -> sprintf "(%s %s)" (string_of_un_op g) (f x)
   | Fix(e), _ -> sprintf "fix(%s)" (f e)
   | Seq(Scopeful, es), _ -> sprintf "(#%s)" (f_list es (String.concat ~sep:";"))
   | Seq(Scopeless, es), _ -> sprintf "(%s)" (f_list es (String.concat ~sep:";"))
   | If(test, _then, _else), _ -> 
         sprintf 
         "if %s: %s else: %s"
         (f test)
         (f _then)
         (f _else)
   | Tuple(es), _ ->
         sprintf "(%s)" (f_list es (String.concat ~sep:","))
   | KthTuple _, _ -> raise Unimplemented
   | List(es), _ -> 
         sprintf "[%s]" (f_list es (String.concat ~sep:","))
   | LamPat(pats, body), _ -> 
         sprintf "fn(%s): %s"
         (f_list pats (String.concat ~sep:","))
         (f body)
   | Call(id, es), _ -> 
      sprintf "%s(%s)"
      (f id)
      (f_list es (String.concat ~sep:","))
   | BindMatch(lhs_patc, rhs), _ -> sprintf "%s=%s" (f lhs_patc) (f rhs)
   | TypeAnnotated(inner, ty), _ -> sprintf "(%s::%s)" (f inner) (pretty_print_type ty)
   | CaseMatch _, _ -> raise Unimplemented
   | Assert _, _ -> raise Unimplemented
   | With _, _ -> raise Unimplemented


let rec ast_format: 't. ('t, 'top) gen_ast -> string = fun e ->
   shallow_format {f = ast_format} e
