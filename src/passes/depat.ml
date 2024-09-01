open Core
open Oyula_lib.Ast

exception Unimplemented

type src = top
type dst = <
   typed: yes;
   pattern: no;
   currying: no;
   scoped_seq: no;
   letin: no>

let rec depat: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun tree ->
   let _sha_de_seq: (ty, src, dst) flex_ast -> (ty, dst) gen_ast = shallow_map {f = depat} in
   let _list_de_seq: type ty2. (ty2, src) gen_ast list -> (ty2, dst) gen_ast list = List.map ~f:depat in
   raise Unimplemented
