open Ast

type associativity = Left | Right

type binary_operator = 
   {
      name: string;
      precedence: int;
      assoc: associativity;
      type_signature: yula_type;
   }

module StrMap = Map.Make(String) 

type binop_map = binary_operator StrMap.t

let type_comparator () =
   let var = gen_tvar () in
   TForall(TypeVarSet.singleton var, TArrow(TVar var, TArrow(TVar var, t_bool)))

let binop_list = 
  (* NOTE:
     1. The operators have to be ordered by precedence. We use List.group on it
     2. The operators in additionally should be ordered so that any string doesn't have its prefix comes ahead so that parser combinator works
  *)
   [
      {name = "*"; precedence = 960; assoc= Left; type_signature = TArrow(t_int, TArrow(t_int, t_int)) };
      {name = "/"; precedence = 960; assoc= Left; type_signature = TArrow(t_int, TArrow(t_int, t_int)) };

      {name = "-"; precedence = 970; assoc= Left; type_signature = TArrow(t_int, TArrow(t_int, t_int)) };
      {name = "+"; precedence = 970; assoc= Left; type_signature = TArrow(t_int, TArrow(t_int, t_int)) };

      {name = "=="; precedence = 980; assoc= Left; type_signature = type_comparator () };
      {name = "!="; precedence = 980; assoc= Left; type_signature = type_comparator () };
      {name = "<="; precedence = 980; assoc= Left; type_signature = type_comparator () };
      {name = ">="; precedence = 980; assoc= Left; type_signature = type_comparator () };
      {name =  "<"; precedence = 980; assoc= Left; type_signature = type_comparator () };
      {name =  ">"; precedence = 980; assoc= Left; type_signature = type_comparator () };

      {name = "and"; precedence = 990; assoc= Left; type_signature = TArrow(t_bool, TArrow(t_bool, t_bool)) };
      {name = "or"; precedence = 1000; assoc= Left; type_signature = TArrow(t_bool, TArrow(t_bool, t_bool)) };
   ]
let binop_map = 
   binop_list
   |> List.to_seq
   |> Seq.map (fun op -> op.name, op)
   |> StrMap.of_seq

open Core

let binops_ranked =
   List.group binop_list ~break:(fun l_op r_op -> not (phys_equal l_op.precedence r_op.precedence))
