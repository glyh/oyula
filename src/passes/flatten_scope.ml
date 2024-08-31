open Core
open Oyula_lib.Ast

type src = Curryfy.dst
type dst = <
   pattern: no;
   currying: yes;
   scoped_seq: yes;
   letin: no>


let rec flatten_scope: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun tree ->
   let sha_flatten_scope: (ty, src, dst) flex_ast -> (ty, dst) gen_ast = shallow_map {f = flatten_scope} in
   let rec flatten (es: src exp_t list): dst exp_t list =
      List.fold_left
         es
         ~init: []
         ~f:(fun acc ele ->
            match ele with
            | Seq(Scopeless, es) -> acc @ (flatten es)
            | Seq(Scopeful, es) -> acc @ [SeqScope(flatten es)]
            | e -> acc @ [flatten_scope e])
   in
   match tree with
   | Seq(_, es) -> SeqScope(flatten es)
   | Concrete _ as e -> sha_flatten_scope e
   | Gensym _ as e -> sha_flatten_scope e
   | Assert _ as e -> sha_flatten_scope e
   | Val _ as e -> sha_flatten_scope e
   | Lit _ as e -> sha_flatten_scope e
   | Binary _ as e -> sha_flatten_scope e
   | Unary _ as e -> sha_flatten_scope e
   | Fix _ as e -> sha_flatten_scope e
   | If _ as e -> sha_flatten_scope e
   | Tuple _ as e -> sha_flatten_scope e
   | KthTuple _ as e -> sha_flatten_scope e
   | List _ as e -> sha_flatten_scope e
   | Abs _ as e -> sha_flatten_scope e
   | AbsU _ as e -> sha_flatten_scope e
   | App _ as e -> sha_flatten_scope e
   | BindOnly _ as e -> sha_flatten_scope e
   | ConcreteCaseMatch _ as e -> sha_flatten_scope e
