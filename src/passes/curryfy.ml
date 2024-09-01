open Core
open Oyula_lib.Ast

type src = top
type dst = <
   currying: yes;
   scoped_seq: no;
   letin: no;
   typed: no;
   pattern: yes;
>

let rec currify_naked: type ty. (ty, src) naked_gen_ast -> (ty, dst) naked_gen_ast = fun tree ->
   let sha_currify: (ty, src, dst) naked_flex_ast -> (ty, dst) naked_gen_ast = 
      shallow_map_naked {f = currify}
   in
   let list_currify: type ty2. (ty2, src) gen_ast list -> (ty2, dst) gen_ast list = List.map ~f:currify in
   match tree with
   | Call(id, exps) -> 
      let id = currify id in
      begin match list_currify exps with
      | [] -> App((Val id, ann_default), (Lit Unit, ann_default))
      | exps -> List.fold exps ~init:(Val id) ~f:(fun acc ele -> App((acc, ann_default), ele))
      end
   | LamPat(params, body) ->
      let params = list_currify params in
      let body = currify body in
      begin match params with
      | [] -> AbsU(body)
      | params -> 
         let tree, _ =
            List.fold_right
               params
               ~f:(fun pat body -> AbsPat(pat, body), ann_default)
               ~init:body
         in tree
      end

   | Concrete _ as e -> sha_currify e
   | Gensym _ as e -> sha_currify e
   | Assert _ as e -> sha_currify e
   | Val _ as e -> sha_currify e
   | Lit _ as e -> sha_currify e
   | Fix _ as e -> sha_currify e
   | Seq _ as e -> sha_currify e
   | If _ as e -> sha_currify e
   | Tuple _ as e -> sha_currify e
   | IndexTuple _ as e -> sha_currify e
   | List _ as e -> sha_currify e
   | Bind _ as e -> sha_currify e
   | Lens _ as e -> sha_currify e
   | Union _ as e -> sha_currify e
   | Updatable _ as e -> sha_currify e
   | Pin _ as e -> sha_currify e
   | PatTuple _ as e -> sha_currify e
   | PatList _ as e -> sha_currify e
   | PLit _ as e -> sha_currify e
   | PAny _ as e -> sha_currify e
   | With _ as e -> sha_currify e
   | PatComplex _ as e -> sha_currify e
   | BindMatch _ as e -> sha_currify e
   | CaseMatch _ as e -> sha_currify e

and currify: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun (ast, AnnEmpty ann_inner) ->
   currify_naked ast, AnnEmpty ann_inner
