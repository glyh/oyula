open Core
open Oyula_lib.Ast

exception Unimplemented

type src = Type_inference.dst
type dst = <
   currying: yes;
   scoped_seq: yes;
   letin: yes;
   typed: yes;
   pattern: no;
>

(*let rec depat_naked: type ty. (ty, src) naked_gen_ast -> (ty, dst) naked_gen_ast = fun tree ->*)
(*   let sha_deseq: (ty, src, dst) naked_flex_ast -> (ty, dst) naked_gen_ast = shallow_map_naked {f = depat} in*)
(*   raise Unimplemented*)
(**)
(*and depat: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun ((ast, AnnEmpty ann) as tree) ->*)
(*   match tree with*)
(*   | BindMatch (_, (rhs, rhs_ann)), ann -> *)
(*      let AnnTyped ann = merge_annotation rhs_ann ann in*)
(*      (* just return rhs as we're in no scope *)*)
(*      depat_naked rhs, AnnEmpty ann*)
(*   | _ -> deseq_naked ast, AnnEmpty ann*)
