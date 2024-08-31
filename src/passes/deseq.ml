open Core
open Oyula_lib.Ast

exception Unreachable

type src = Flatten_scope.dst
type dst = <
   pattern: no;
   currying: yes;
   scoped_seq: yes;
   letin: yes>

let rec deseq_naked: type ty. (ty, src) naked_gen_ast -> (ty, dst) naked_gen_ast = fun tree ->
   let sha_deseq: (ty, src, dst) naked_flex_ast -> (ty, dst) naked_gen_ast = shallow_map_naked {f = deseq} in
   match tree with
   | SeqScope es ->
      begin match List.rev es with
        | [] ->
           Lit Unit
        | e :: es ->
           let _, whole_ann = deseq e in
           let folded, _ = 
              List.fold_left es
                 ~init:(deseq e)
                 ~f:(fun acc ele -> 
                    match ele with
                    | BindOnly(lhs, rhs), _ -> LetIn(deseq lhs, deseq rhs, acc), whole_ann
                    | _ -> LetIn((Concrete "_", ann_id_0), deseq ele, acc), whole_ann)
            in folded
     end
   | BindOnly (_, (rhs, _)) ->
      deseq_naked rhs (* just return rhs as we're in no scope *)

   | Concrete _ as e -> sha_deseq e
   | Gensym _ as e -> sha_deseq e
   | Assert _ as e -> sha_deseq e
   | Val _ as e -> sha_deseq e
   | Lit _ as e -> sha_deseq e
   | Binary _ as e -> sha_deseq e
   | Unary _ as e -> sha_deseq e
   | Fix _ as e -> sha_deseq e
   | If _ as e -> sha_deseq e
   | Tuple _ as e -> sha_deseq e
   | KthTuple _ as e -> sha_deseq e
   | List _ as e -> sha_deseq e
   | Abs _ as e -> sha_deseq e
   | AbsU _ as e -> sha_deseq e
   | App _ as e -> sha_deseq e
   | ConcreteCaseMatch _ as e -> sha_deseq e

and deseq: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun tree ->
   let ast, ann = tree
   in deseq_naked ast, ann
