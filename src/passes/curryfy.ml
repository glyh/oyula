open Core
open Oyula_lib.Ast

type src = Depat.dst
type dst = <
   pattern: no;
   currying: yes;
   scoped_seq: no;
   letin: no>

let rec currify_naked: type ty. (ty, src) naked_gen_ast -> (ty, dst) naked_gen_ast = fun tree ->
   let sha_currify: (ty, src, dst) naked_flex_ast -> (ty, dst) naked_gen_ast = 
      shallow_map_naked {f = currify}
   in
   let list_currify: type ty2. (ty2, src) gen_ast list -> (ty2, dst) gen_ast list = List.map ~f:currify in
   match tree with
   | Call(id, exps) -> 
      let id = currify id in
      begin match list_currify exps with
      | [] -> App((Val id, ann_exp_0), (Lit Unit, ann_exp_0))
      | exps -> List.fold exps ~init:(Val id) ~f:(fun acc ele -> App((acc, ann_exp_0), ele))
      end
   | Lam(params, body) ->
      let params = list_currify params in
      let body = currify body in
      begin match params with
      | [] -> AbsU(body)
      | params -> 
         let tree, _ =
            List.fold_right
               params
               ~f:(fun var body -> Abs(var, body), ann_exp_0)
               ~init:body
         in tree
      end

   | Concrete _ as e -> sha_currify e
   | Gensym _ as e -> sha_currify e
   | Assert _ as e -> sha_currify e
   | Val _ as e -> sha_currify e
   | Lit _ as e -> sha_currify e
   | Binary _ as e -> sha_currify e
   | Unary _ as e -> sha_currify e
   | Fix _ as e -> sha_currify e
   | Seq _ as e -> sha_currify e
   | If _ as e -> sha_currify e
   | Tuple _ as e -> sha_currify e
   | KthTuple _ as e -> sha_currify e
   | List _ as e -> sha_currify e
   | BindOnly _ as e -> sha_currify e
   | ConcreteCaseMatch _ as e -> sha_currify e

and currify: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun tree ->
   let ast, ann = tree
   in currify_naked ast, ann
