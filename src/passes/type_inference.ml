open Oyula_lib.Ast
open Oyula_lib.Pretty_print

exception Unreachable

(*NOTE: 
  This typechecker is loosely based on:
  - https://github.com/glyh/wyah/blob/master/lib/type_environment.ml
  Some references:
  - https://course.ccs.neu.edu/cs4410/lec_type-inference_notes.html
  - https://cs3110.github.io/textbook/chapters/interp/inference.html
*)

type src = Deseq.dst
type dst = <
   currying: yes;
   scoped_seq: yes;
   letin: yes;
   typed: yes;
   pattern: yes;
>

module TypeEnv = Base_Map.Make(struct 
  type t = src id_t
  let compare = poly_compare
end)

type type_env = yula_type TypeEnv.t

exception UndefinedVariable of src id_t
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
  | TTupleCons(car, cdr) ->
      TypeVarSet.union (free_variables car) (free_variables cdr)
  | TUnion tys ->
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
  | TTupleCons(lhs, rhs) -> TTupleCons(f lhs, f rhs)
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
  | TTupleCons (l1, l2), TTupleCons(r1, r2) ->
      None, [l1, r1; l2, r2]

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

let generalize (cs: type_constraint list) (env: type_env) (var: src id_t) (ty: yula_type): type_env = 
  let sub_solved = unify cs in
  let env_new = apply_sub_env sub_solved env in
  let fv_env_new = free_variables_env env_new in
  let ty_new = apply_sub_ty sub_solved ty in
  let fv_ty_new = free_variables ty_new in 
  let vars_to_generalize = TypeVarSet.diff fv_ty_new fv_env_new in
  let ty_generalized = TForall(vars_to_generalize, ty_new) in
  TypeEnv.add var ty_generalized env_new

let rec inference_constraints_pat: 
  type_env -> 
  src pat_t -> 
  (yula_type * type_constraint list * type_env) = 
  fun tenv tree ->
  let tree_naked, _ = tree in
  match tree_naked with
  | Updatable _ -> raise Unimplemented 

let inference_constraints_pat_complex: 
  type_env -> 
  src pat_complex_t -> 
  (yula_type * type_constraint list * type_env) = 
  fun tenv tree ->
  let (PatComplex (pc1, pc_rest), AnnEmpty {ast_type}) = tree in
  let rec go acc lst =
    match lst with
    | [] -> acc
    | pat :: rest -> 
      let (tys_acc, cons_acc, env_acc) = acc in
      let (pat_ty, pat_cons, env') = inference_constraints_pat env_acc pat in
      go (pat_ty :: tys_acc, cons_acc @ pat_cons, env') rest
  in
  let (pc_tys, pc_conses, env') = go ([], [], tenv) (pc1 :: pc_rest)
  in
  let (inferred_ty, cons, env') = 
  match pc_tys with
  | [] -> raise Unreachable
  | ty_hd :: ty_rest -> 
      ty_hd, (List.map (fun pty -> (pty, ty_hd)) ty_rest) @ pc_conses, env'
  in
  begin match ast_type with
  | None -> inferred_ty, cons, env'
  | Some annotated_type -> annotated_type, (inferred_ty, annotated_type) :: cons, env'
  end

let rec inference_constraints (tenv: type_env) (tree: src exp_t): (yula_type * type_constraint list) = 
  let inference_constraints_inner tenv tree = 
    let tree_naked, _ = tree in
    match tree_naked with
    | Lit (Unit) -> t_unit, []
    | Lit (Int _) -> t_int, []
    | Lit (Char _) -> t_char, []
    | Lit (Bool _) -> t_bool, []
    | Lit (F64 _) -> t_f64, []
    | Lit (Str _) -> t_string, []
    | Lit (Keyword _) -> t_keyword, []

    | Fix(lam) ->  (* fix: (A -> B) -> B *)
        let f_gen (* B *)= TVar (gen_tvar ()) in
        let wrapped_gen (* A *) = TVar (gen_tvar ()) in
        let (lam_ty (* A -> B *), lam_cons) = inference_constraints tenv lam in
        f_gen, (lam_ty, TArrow(wrapped_gen, f_gen)) :: lam_cons

    | Val(var) -> 
        begin match TypeEnv.find_opt var tenv with
        | None -> raise (UndefinedVariable(var))
        | Some(scheme) -> instantiate(scheme), []
        end

    | If(cond, then_clause, else_clause) ->
        let (cond_ty, cond_cons) = inference_constraints tenv cond in
        let (then_ty, then_cons) = inference_constraints tenv then_clause in
        let (else_ty, else_cons) = inference_constraints tenv else_clause in
        then_ty, [(cond_ty, t_bool); (then_ty, else_ty)] @ cond_cons @ then_cons @ else_cons

    | Assert inner ->
        let (inner_ty, inner_cons) = inference_constraints tenv inner in
        t_bool, (t_bool, inner_ty) :: inner_cons

    | Tuple (e1, e2, e_rest) ->
        let (car_ty, car_cons) = inference_constraints tenv e1 in
        let cdr = match e_rest with
        | [] -> e2
        | hd :: rest -> Tuple (e2, hd, rest), ann_default
        in
        let (cdr_ty, cdr_cons) = inference_constraints tenv cdr in
        TTupleCons (car_ty, cdr_ty), car_cons @ cdr_cons

    | IndexTuple (tup, i) ->
        let tup_ty, tup_cons = inference_constraints tenv tup in
        let gen_indexed = TVar (gen_tvar ()) in
        let gen_rest = TVar (gen_tvar ()) in
        let rec gen_wrap ty i = 
          if i == 0 then ty
          else TTupleCons(TVar (gen_tvar ()), gen_wrap ty (i - 1))
        in
        gen_indexed, (gen_wrap (TTupleCons (gen_indexed, gen_rest)) i, tup_ty) :: tup_cons 

    | List l ->
        begin match l with
        | [] -> 
            let ele_ty = gen_tvar () in
            TForall(TypeVarSet.singleton ele_ty, TList (TVar ele_ty)), []
        | hd :: rest ->
            let hd_ty, hd_cons = inference_constraints tenv hd in
            let rest_ty, rest_cons = List.map (inference_constraints tenv) rest |> List.split in
            TList hd_ty, (List.map (fun ty -> (ty, hd_ty)) rest_ty) @ hd_cons @ (List.concat rest_cons)
        end

    | AbsU(bdy) ->
        let bdy_ty, bdy_cons = inference_constraints tenv bdy in
        TArrow(t_unit, bdy_ty), bdy_cons

    | AbsPat(pat, bdy) ->
      let pat_ty, pat_cons, tenv' = inference_constraints_pat_complex tenv pat in
      let bdy_ty, bdy_cons = inference_constraints tenv' bdy in
      TArrow(pat_ty, bdy_ty), pat_cons @ bdy_cons

    | App(f, x) -> 
        let (f_ty, f_cons) = inference_constraints tenv f in
        let (x_ty, x_cons) = inference_constraints tenv x in
        let var_gen = TVar (gen_tvar ()) in
        var_gen, [(f_ty, TArrow(x_ty, var_gen))] @ f_cons @ x_cons

    | LetInPat(pat, rhs, bdy) ->
        let rhs_ty, rhs_cons = inference_constraints tenv rhs in
        let pat_ty, pat_cons, tenv' = inference_constraints_pat_complex tenv pat in
        let bdy_ty, bdy_cons = inference_constraints tenv' bdy in
        bdy_ty, (rhs_ty, pat_ty) :: rhs_cons @ pat_cons @ bdy_cons

    | CaseMatch(matched, branches) ->
        let matched_ty, matched_cons = inference_constraints tenv matched in

        let (info1_ret, info1_cons), info_rest = list_1_map 
          (fun (pat, guard, ret) ->
            let pat_ty, pat_cons, tenv' = inference_constraints_pat_complex tenv pat in
            let guard_ty, guard_cons = inference_constraints tenv guard in
            let ret_ty, ret_cons = inference_constraints tenv' ret in
            ret_ty, [pat_ty, matched_ty; guard_ty, t_bool] @ pat_cons @ guard_cons @ ret_cons)
          branches
        in 
        let ret_tys, conses = info_rest |> List.split 
        in 
        info1_ret,
        (List.map (fun ty -> (ty, info1_ret)) ret_tys)
        @ info1_cons
        @ (conses |> List.concat)
        @ matched_cons
  in 
  let inferred_type, cons = inference_constraints_inner tenv tree in
  let _, AnnEmpty { ast_type } = tree in
  match ast_type with
  | None -> inferred_type, cons
  | Some annotated_type -> annotated_type, (inferred_type, annotated_type) :: cons

let show_cons ((tlhs, trhs): type_constraint): string = 
  pretty_print_type tlhs ^ " = " ^ pretty_print_type trhs

let show_sub (smap: subst): string =
  MapSubs.fold
  (fun k v acc -> Printf.sprintf "%s -> %s\n%s" k (pretty_print_type v) acc)
  smap
  ""

let inference_type (tenv: type_env) (exp: src exp_t): yula_type = 
  let (exp_ty, cons) = inference_constraints tenv exp in
  let sub = unify cons in 
  let type_sub = apply_sub_ty sub exp_ty in
  let rest_fvs = (free_variables type_sub) in
  if compare rest_fvs TypeVarSet.empty == 0
  then type_sub
  else TForall (rest_fvs, type_sub)
