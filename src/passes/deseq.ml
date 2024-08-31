open Core
open Oyula_lib.Ast

exception Unreachable

type src = Flatten_scope.dst
type dst = <
   pattern: no;
   currying: yes;
   scoped_seq: yes;
   letin: yes>

let rec deseq: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun tree ->
   let sha_deseq: (ty, src, dst) flex_ast -> (ty, dst) gen_ast = shallow_map {f = deseq} in
   match tree with
   | SeqScope es ->
      begin match List.rev es with
        | [] ->
           Lit Unit
        | e :: es ->
           List.fold_left es
           ~init:(deseq e)
           ~f:(fun acc ele -> 
              match ele with
              | BindOnly(lhs, rhs) -> LetIn(deseq lhs, deseq rhs, acc)
              | _ -> LetIn(Concrete "_", deseq ele, acc))
     end
   | BindOnly _ ->
      raise Unreachable (* Shouldn't be reaching a bind inside no scope *)

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
