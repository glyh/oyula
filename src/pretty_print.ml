
open Ast
open Operators

let lst_of_seq = List.of_seq

open Core

let pretty_print_var_set (s: type_var_set) =
  s
  |> TypeVarSet.to_seq
  |> lst_of_seq
  |> String.concat ~sep:","

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
  | TTupleCons _ as ty ->
      let rec gen acc ty =
         match ty with 
         | TTupleCons (car, cdr) -> gen (acc ^ ((pretty_print_type car) ^ ",")) cdr
         | ty -> acc ^ (pretty_print_type ty) ^ ")"
      in gen "(" ty
  | TUnion(tys) -> (List.map ~f:pretty_print_type tys |> String.concat ~sep:" | ")
  | TTagged(tag, ty) -> Printf.sprintf ":%s(%s)" tag (pretty_print_type ty)
  | TCon ty -> ty

let string_of_atom (a: atom) = 
   match a with
   | Int i -> string_of_int i
   | F64 f -> string_of_float f
   | Str s -> sprintf {|"%s"|} (escape s)
   | Keyword k -> ":" ^ k
   | Bool true -> "true"
   | Bool false -> "false"
   | Unit -> "()"
   | Char c -> sprintf {|'%s'|} (append_escape "" c)

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
   | Fix(e), _ -> sprintf "fix(%s)" (f e)
   | Seq(Scopeful, es), _ -> sprintf "(#%s)" (f_list es (String.concat ~sep:";"))
   | Seq(Scopeless, es), _ -> sprintf "(%s)" (f_list es (String.concat ~sep:";"))
   | If(test, _then, _else), _ -> 
         sprintf 
         "if %s: %s else: %s"
         (f test)
         (f _then)
         (f _else)
   | Tuple(e1, e2, e_rest), _ ->
         sprintf "(%s)" (f_list (e1 :: e2 :: e_rest) (String.concat ~sep:","))
   | IndexTuple _, _ -> raise Unimplemented
   | List(es), _ -> 
         sprintf "[%s]" (f_list es (String.concat ~sep:","))
   | LamPat(pats, body), _ -> 
         sprintf "fn(%s): %s"
         (f_list pats (String.concat ~sep:","))
         (f body)
   | Call((Concrete op, _), [lhs; rhs]), _ when StrMap.mem op binop_map ->
      sprintf "(%s %s %s)" (f lhs) op (f rhs)

   | Call(id, es), _ -> 
      sprintf "%s(%s)"
      (f id)
      (f_list es (String.concat ~sep:","))
   | BindMatch(lhs_patc, rhs), _ -> sprintf "%s=%s" (f lhs_patc) (f rhs)
   | CaseMatch _, _ -> raise Unimplemented
   | Assert _, _ -> raise Unimplemented
   | With _, _ -> raise Unimplemented

let rec ast_format: 't. ('t, 'top) gen_ast -> string = fun e ->
   shallow_format {f = ast_format} e
