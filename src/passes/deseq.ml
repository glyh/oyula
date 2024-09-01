open Core
open Oyula_lib.Ast

exception Unreachable

type src = Flatten_scope.dst
type dst = <
   currying: yes;
   scoped_seq: yes;
   letin: yes;
   typed: no;
   pattern: yes;
>

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
                    | BindMatch((patc, ann_patc), rhs), ann_bindmatch -> 
                        let AnnEmpty ann1 = ann_patc in
                        let AnnEmpty ann2 = ann_bindmatch in
                        let AnnEmpty ann_merged = merge_annotation (AnnEmpty ann1) (AnnEmpty ann2) in
                       LetInPat((deseq_naked patc, AnnEmpty ann_merged), deseq rhs, acc), whole_ann
                    | _, AnnEmpty ann_rhs -> 
                      let pc = ((PatComplex ((PAny(), AnnEmpty ann_rhs), [])), AnnEmpty ann_rhs) in
                       LetInPat(pc , deseq ele, acc), whole_ann)
            in folded
     end
   | BindMatch _ -> raise Unreachable (* this case is dealt in `deseq` *)
   | PatComplex _ as e -> sha_deseq e

   | Concrete _ as e -> sha_deseq e
   | Gensym _ as e -> sha_deseq e
   | Assert _ as e -> sha_deseq e
   | Val _ as e -> sha_deseq e
   | Lit _ as e -> sha_deseq e
   | Fix _ as e -> sha_deseq e
   | If _ as e -> sha_deseq e
   | Tuple _ as e -> sha_deseq e
   | IndexTuple _ as e -> sha_deseq e
   | List _ as e -> sha_deseq e
   | AbsU _ as e -> sha_deseq e
   | App _ as e -> sha_deseq e

   | Bind _ as e -> sha_deseq e
   | Lens _ as e -> sha_deseq e
   | Union _ as e -> sha_deseq e
   | Updatable _ as e -> sha_deseq e
   | Pin _ as e -> sha_deseq e
   | PatTuple _ as e -> sha_deseq e
   | PatList _ as e -> sha_deseq e
   | PLit _ as e -> sha_deseq e
   | PAny _ as e -> sha_deseq e
   | With _ as e -> sha_deseq e
   | AbsPat _ as e -> sha_deseq e
   | CaseMatch _ as e -> sha_deseq e

and deseq: type ty. (ty, src) gen_ast -> (ty, dst) gen_ast = fun ((ast, AnnEmpty ann) as tree) ->
   match tree with
   | BindMatch (_, (rhs, rhs_ann)), ann -> 
      let AnnEmpty ann = merge_annotation rhs_ann ann in
      (* just return rhs as we're in no scope *)
      deseq_naked rhs, AnnEmpty ann
   | _ -> deseq_naked ast, AnnEmpty ann
