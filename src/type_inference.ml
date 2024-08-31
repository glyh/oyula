open Ast

(*NOTE: 
  This typechecker is loosely based on:
  - https://github.com/glyh/wyah/blob/master/lib/type_environment.ml
  Some references:
  - https://course.ccs.neu.edu/cs4410/lec_type-inference_notes.html
  - https://cs3110.github.io/textbook/chapters/interp/inference.html
*)

exception UndefinedVariable of string
exception Unimplemented
exception NotEnoughConstraint of yula_type

type type_constraint = yula_type * yula_type

exception UnificationFailure of type_constraint

let rec free_variables (scheme: yula_type): type_var_set = 
  match scheme with
  | TForall(vars, inner) -> TypeVarSet.diff (free_variables inner) vars
  | TVar(v) -> TypeVarSet.singleton v
  | TArrow(lhs, rhs) -> TypeVarSet.union (free_variables lhs) (free_variables rhs)
  | TList(inner) -> free_variables inner
  | TTuple tys | TUnion tys ->
      tys
      |> List.map free_variables
      |> List.fold_left TypeVarSet.union TypeVarSet.empty
  | TTagged (_, inner) -> free_variables inner
  | TCon _ -> TypeVarSet.empty

let free_variables_env (env: type_env): type_var_set = 
  TypeEnv.fold
    (fun _ v acc -> TypeVarSet.union acc (free_variables v))
    env
    TypeVarSet.empty

module MapSubs = Map.Make(struct
  type t = tvar
  let compare = compare
end)
type subst = yula_type MapSubs.t

let rec apply_sub_ty (m: subst) (inner_ty: yula_type): yula_type =
  let f = apply_sub_ty m in
  let f_list = List.map f in
  match inner_ty with
  | TForall(vs, inner) -> TForall(vs, f inner) 
  | TVar(v) ->
      begin match MapSubs.find_opt v m with
      | None -> TVar(v)
      | Some(w) -> w
      end
  | TArrow(lhs, rhs) -> TArrow(f lhs, f rhs)
  | TList(ty) -> TList(f ty)
  | TTuple(tys) -> TTuple(f_list tys)
  | TUnion(tys) -> TUnion(f_list tys)
  | TTagged(tag, ty) -> TTagged(tag, f ty)
  | TCon _ as ty -> ty

let instantiate (scheme: yula_type): yula_type = 
  match scheme with
  | TForall(vars, inner) -> 
      let vars_pair = 
        vars
        |> TypeVarSet.to_seq
        |> Seq.map (fun v -> (v, TVar (gen_tvar ())))
        |> MapSubs.of_seq
      in
        apply_sub_ty vars_pair inner
  | t -> t

let rec unify_one (c: type_constraint): (tvar * yula_type) option * type_constraint list =
  match c with
  | (lhs, rhs) when compare lhs rhs == 0 ->
      None, []
  | (TForall (vs1, inner1),TForall (vs2, inner2)) when compare vs1 vs2 == 0 ->
      unify_one (inner1, inner2)

  | ((TVar v, ty) | (ty, TVar v)) ->
      if not (TypeVarSet.mem v (free_variables ty)) then
        Some (v, ty), []
      else
        raise (UnificationFailure c)
  | (TArrow(l1, l2), TArrow (r1, r2)) ->
      None, [l1, r1; l2, r2]
  | (TList(lhs), TList (rhs)) ->
      unify_one (lhs, rhs)
  | (TTuple(tys_left), TTuple(tys_right)) when (List.length tys_left) == (List.length tys_right) ->
      None, List.combine tys_left tys_right

  (* what to do with unions? *)
  | (TTagged(tag1, ty1), TTagged(tag2, ty2)) when compare tag1 tag2 == 0 ->
      unify_one (ty1, ty2)

  | (TCon lhs, TCon rhs) when lhs == rhs ->
        None, []
  | _ ->
        raise (UnificationFailure (c))

let apply_sub_sub (s_applied: subst) (s_target: subst): subst = 
  s_target
  |> MapSubs.map (apply_sub_ty s_applied)

let apply_sub_cs (s: subst) (cs: type_constraint list): type_constraint list =
  cs
  |> List.map (fun (tlhs, trhs) -> (apply_sub_ty s tlhs, apply_sub_ty s trhs)) 

let apply_sub_env (s: subst) (env: type_env): type_env = 
  TypeEnv.map (apply_sub_ty s) env

let rec unify (cs: type_constraint list): subst = 
  match cs with
  | [] -> MapSubs.empty
  | c :: cs ->
    begin match unify_one c with
    | Some(s_v, s_t), cs_new -> MapSubs.add s_v s_t (unify (cs_new @ (apply_sub_cs (MapSubs.singleton s_v s_t) cs)))
    | None, cs_new -> unify (cs_new @ cs)
    end

let rec generalize (cs: type_constraint list) (env: type_env) (var: top id_t) (ty: yula_type): type_env = 
  let sub_solved = unify cs in
  let env_new = apply_sub_env sub_solved env in
  let fv_env_new = free_variables_env env_new in
  let ty_new = apply_sub_ty sub_solved ty in
  let fv_ty_new = free_variables ty_new in 
  let vars_to_generalize = TypeVarSet.diff fv_ty_new fv_env_new in
  let ty_generalized = TForall(vars_to_generalize, ty_new) in
  TypeEnv.add var ty_generalized env_new

type src = top
(*type dst = <*)
(*   typed: yes;*)
(*   pattern: yes;*)
(*   currying: no;*)
(*   scoped_seq: no;*)
(*   letin: no>*)
type dst = src

let rec inference_constraints: 
  type ty. 
  type_env -> 
  (ty, src) gen_ast -> 
  (yula_type * type_constraint list) = 
  fun tenv tree ->
  let tree_naked, _ = tree in
  match tree_naked with
  | Lit (Unit) -> (t_unit, [])
  | Lit(Int _) -> (t_int, [])
  | Lit(Char _) -> (t_char, [])
  | Lit(Bool _) -> (t_bool, [])

  | Fix(lam) ->
      let f_gen = TVar (gen_tvar ()) in
      let wrapped_gen = TVar (gen_tvar ()) in
      let (lam_ty, lam_cons) = inference_constraints tenv lam in
      f_gen, (lam_ty, TArrow(wrapped_gen, f_gen)) :: lam_cons

  | Val(var) -> 
      begin match TypeEnv.find_opt var tenv with
      | None -> raise (UndefinedVariable(var))
      | Some(scheme) -> (instantiate(scheme), [])
      end

  | Lam(var, body) -> 
      let var_gen = TVar (gen_tvar ()) in
      let tenv_new = 
        TypeEnv.add var var_gen tenv
      in
      let (body_type, constraints) = 
        inference_constraints tenv_new body
      in
      (TArrow(var_gen, body_type), constraints)

  | If(cond, then_clause, else_clause) ->
      let (cond_ty, cond_cons) = inference_constraints tenv cond in
      let (then_ty, then_cons) = inference_constraints tenv then_clause in
      let (else_ty, else_cons) = inference_constraints tenv else_clause in
      (then_ty, [(cond_ty, t_bool); (then_ty, else_ty)] @ cond_cons @ then_cons @ else_cons)

  | App(f, x) ->
      let (f_ty, f_cons) = inference_constraints tenv f in
      let (x_ty, x_cons) = inference_constraints tenv x in
      let var_gen = TVar (gen_tvar ()) in
      (var_gen, [(f_ty, TArrow(x_ty, var_gen))] @ f_cons @ x_cons)

let show_cons ((tlhs, trhs): type_constraint): string = 
  pretty_print_type tlhs ^ " = " ^ pretty_print_type trhs

let show_sub (smap: subst): string =
  MapSubs.fold
  (fun k v acc ->
    string_of_int k ^ " -> " ^ pretty_print_type v ^ "\n" ^ acc
  )
  smap
  ""

(*let inference_type (tenv: type_env) (exp: expr): wyah_type = *)
(*  let (exp_ty, cons) = inference_constraints tenv exp in*)
(*  let sub = unify cons in *)
(*  let type_sub = apply_sub_ty sub exp_ty in*)
(*  let rest_fvs = (free_variables type_sub) in*)
(*  if compare rest_fvs TypeVarSet.empty == 0*)
(*  then type_sub*)
(*  else TForall (rest_fvs, type_sub)*)
