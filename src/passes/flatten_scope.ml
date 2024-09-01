open Core
open Oyula_lib.Ast

type src = Curryfy.dst
type dst = <
   currying: yes;
   scoped_seq: yes;
   letin: no;
   typed: no;
   pattern: yes;
>


let rec flatten_scope_naked: type ty. (ty, src) naked_gen_ast -> (ty, dst) naked_gen_ast = fun tree ->
   let sha_flatten_scope: (ty, src, dst) naked_flex_ast -> (ty, dst) naked_gen_ast = shallow_map_naked {f = flatten_scope} in
   let rec flatten (es: src exp_t list): dst exp_t list =
      List.fold_left
         es
         ~init: []
         ~f:(fun acc ele ->
            match ele with
            | Seq(Scopeless, es), _ -> acc @ (flatten es)
            | Seq(Scopeful, es), AnnEmpty ann -> acc @ [SeqScope(flatten es), AnnEmpty ann]
            | e -> acc @ [flatten_scope e])
   in
   match tree with
   | Seq(_, es) -> SeqScope(flatten es)
   | Concrete _ as e -> sha_flatten_scope e
   | Gensym _ as e -> sha_flatten_scope e
   | Assert _ as e -> sha_flatten_scope e
   | Val _ as e -> sha_flatten_scope e
   | Lit _ as e -> sha_flatten_scope e
   | Fix _ as e -> sha_flatten_scope e
   | If _ as e -> sha_flatten_scope e
   | Tuple _ as e -> sha_flatten_scope e
   | IndexTuple _ as e -> sha_flatten_scope e
   | List _ as e -> sha_flatten_scope e
   | AbsU _ as e -> sha_flatten_scope e
   | App _ as e -> sha_flatten_scope e
   | Bind _ as e -> sha_flatten_scope e
   | Lens _ as e -> sha_flatten_scope e
   | Union _ as e -> sha_flatten_scope e
   | Updatable _ as e -> sha_flatten_scope e
   | Pin _ as e -> sha_flatten_scope e
   | PatTuple _ as e -> sha_flatten_scope e
   | PatList _ as e -> sha_flatten_scope e
   | PLit _ as e -> sha_flatten_scope e
   | PAny _ as e -> sha_flatten_scope e
   | With _ as e -> sha_flatten_scope e
   | PatComplex _ as e -> sha_flatten_scope e
   | AbsPat _ as e -> sha_flatten_scope e
   | BindMatch _ as e -> sha_flatten_scope e
   | CaseMatch _ as e -> sha_flatten_scope e

and flatten_scope: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun (ast, AnnEmpty ann_inner) ->
   flatten_scope_naked ast, AnnEmpty ann_inner
