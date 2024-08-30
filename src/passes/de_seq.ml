open Core
open Oyula_lib.Ast

type src = top
type dst = <
   seq: no;
   pattern: yes;
   lambda: yes;
   call: yes;
   recbind: yes; 
   unique_id: no;
   bind_only: no;
   letin: no>

let rec de_seq: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun tree ->
   let sha_de_seq: (ty, src, dst) flex_ast -> (ty, dst) gen_ast = shallow_map {f = de_seq} in
   let list_de_seq: type ty2. (ty2, src) gen_ast list -> (ty2, dst) gen_ast list = List.map ~f:de_seq in
   match tree with
   | IfSeq(test, _then, _else) -> 
      If(de_seq test, Seq(Scopeful, list_de_seq _then), Seq(Scopeful, list_de_seq _else))
   | LamPatSeq(pats, exps) -> LamPat(list_de_seq pats, Seq(Scopeful, list_de_seq exps))
   | CaseMatchSeq(e, branches) ->
      let branch_de_seq (pat, guard, body) = (de_seq pat, de_seq guard, Seq(Scopeful, list_de_seq body)) in
         CaseMatch(de_seq e, List.map ~f:branch_de_seq branches)

   | Bind _ as e -> sha_de_seq e
   | Lens _ as e -> sha_de_seq e
   | Union _ as e -> sha_de_seq e
   | Updatable _ as e -> sha_de_seq e
   | Pin _ as e -> sha_de_seq e
   | PatTuple _ as e -> sha_de_seq e
   | PatList _ as e -> sha_de_seq e
   | PLit _ as e -> sha_de_seq e
   | PAny _ as e -> sha_de_seq e
   | With _ as e -> sha_de_seq e
   | Val _ as e -> sha_de_seq e
   | Lit _ as e -> sha_de_seq e
   | Binary _ as e -> sha_de_seq e
   | Unary _ as e -> sha_de_seq e
   | Seq _ as e -> sha_de_seq e
   | Tuple _ as e -> sha_de_seq e
   | List _ as e -> sha_de_seq e
   | Call _ as e -> sha_de_seq e
   | BindMatch _ as e -> sha_de_seq e
   | KthTuple _ as e -> sha_de_seq e
   | Concrete _ as e -> sha_de_seq e
   | Gensym _ as e -> sha_de_seq e
   | Assert _ as e -> sha_de_seq e
   | PatComplex _ as p -> sha_de_seq p
   | Fix _ as p -> sha_de_seq p
