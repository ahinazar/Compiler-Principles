(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "tag-parser.ml";;
 open Tag_Parser;;
 open Printf;;
let () = Printexc.record_backtrace true;;
 type var = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | Const' of constant
   | Var' of var
   | Box' of var
   | BoxGet' of var
   | BoxSet' of var * expr'
   | If' of expr' * expr' * expr'
   | Seq' of expr' list
   | Set' of expr' * expr'
   | Def' of expr' * expr'
   | Or' of expr' list
   | LambdaSimple' of string list * expr'
   | LambdaOpt' of string list * string * expr'
   | Applic' of expr' * (expr' list)
   | ApplicTP' of expr' * (expr' list);;
 
 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | Const' Void, Const' Void -> true
   | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
   | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
   | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
   | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
   | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                             (expr'_eq th1 th2) &&
                                               (expr'_eq el1 el2)
   | (Seq'(l1), Seq'(l2)
   | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
   | (Set'(var1, val1), Set'(var2, val2)
   | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                              (expr'_eq val1 val2)
   | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr'_eq body1 body2)
   | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr'_eq body1 body2)
   | Applic'(e1, args1), Applic'(e2, args2)
   | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
      (List.for_all2 expr'_eq args1 args2)
   | _ -> false;;
   
 exception X_syntax_error;;

 let rec get_minor var_name minor lst= match lst with
 | [] -> -1
 | hd::tl when hd=var_name-> minor
 | hd::tl -> get_minor var_name (minor+1) tl;;
 
 let rec var_addr_handler var_name args major =
   if (Array.length args == major) 
       then VarFree(var_name)
   else(
     let minor = get_minor var_name 0 args.(major) in
     if (minor <> -1) 
       then (if (major==0) 
                     then VarParam (var_name,minor) 
                 else VarBound (var_name,(major - 1),minor))
      else var_addr_handler var_name args (major + 1));;
 
let rec lexical_addr_handler expr args= match expr with
   | Const(sexp) -> Const'(sexp)
   | Var(var_name) -> Var'(var_addr_handler var_name args 0)
   | If(test,dit,dif) -> If'(lexical_addr_handler test args , lexical_addr_handler dit args, lexical_addr_handler dif args)
   | Seq(exp_list) -> Seq'(List.map (fun a -> lexical_addr_handler a args) exp_list)
   | Set(var,exp) -> Set'(lexical_addr_handler var args , lexical_addr_handler exp args)
   | Def(name,value) -> Def'(lexical_addr_handler name args , lexical_addr_handler value args)
   | Or(exp_list) -> Or'(List.map (fun a -> lexical_addr_handler a args) exp_list)
   | LambdaSimple(params,body) -> LambdaSimple'(params, lexical_addr_handler body (Array.append [|params|] (Array.append args [||])))
   | LambdaOpt(params,opt,body) -> LambdaOpt'(params,opt,lexical_addr_handler body (Array.append [|params@[opt]|] (Array.append args [||])))
   | Applic(oper,rands) -> Applic'(lexical_addr_handler oper args, List.map (fun a -> lexical_addr_handler a args) rands);;
 
   let rec get_last_exp lst = match lst with
      | [e] -> e
      | _::tl -> get_last_exp tl
      | _-> raise X_syntax_error;;    

   let rec remove_last_exp lst = match lst with
      | [e;_] -> [e]
      | e::tl -> [e]@remove_last_exp tl
      | _-> raise X_syntax_error;;

   let rec tail_calls_handler expr' tp = match expr' with
   | Const'(exp) -> expr'
   | Var'(var_name) -> expr'
   | If'(test,dit,dif) -> If'(tail_calls_handler test false, tail_calls_handler dit tp, tail_calls_handler dif tp)
   | Seq'(exp_list) -> let last_removed = remove_last_exp exp_list in
                                let  last_exp = get_last_exp exp_list in
                                Seq'((List.map (fun a -> tail_calls_handler a false) last_removed)@[tail_calls_handler last_exp tp])
   | Set'(var,exp) -> Set'(var,tail_calls_handler exp false)
   | Def'(name,value) -> Def' (name, tail_calls_handler value tp)
   | Or'(exp_list) -> let last_removed = remove_last_exp exp_list in
                              let  last_exp = get_last_exp exp_list in
                              Or'((List.map (fun a -> tail_calls_handler a false) last_removed)@[tail_calls_handler last_exp tp]) (*maybe to be changed*)
   | LambdaSimple'(params,body) -> LambdaSimple' (params, tail_calls_handler body true) 
   | LambdaOpt'(params,opt,body) -> LambdaOpt'(params,opt, tail_calls_handler body true)
   | Applic'(oper,rands) -> if (tp == true)
                                         then ApplicTP' (tail_calls_handler oper false, List.map (fun a -> tail_calls_handler a false) rands)
                                      else Applic' (tail_calls_handler oper false,  List.map (fun a -> tail_calls_handler a false) rands)  
   | _ -> raise X_syntax_error;;

let check_equ_major param var = match var,param with
  | VarBound(v1,mj,mn),(name,mj2,num) when (v1 = name) &&(mj = mj2)-> [-1]
  | VarParam(v1,mn),(name,-1,num) when (v1 = name) -> [-1]
  | _ ,_-> [];;

let inc_count count =
  count := !count + 1;
  count;;

let rec is_read param body count  = match body with
  | Const'(exp)-> []
  | Var'(exp) -> (check_equ_major param exp)
  | Set'(var,exp) -> is_read param exp count
  | If'(test,dit,dif) -> let r_test = is_read param test count in
                               let r_dit = is_read param dit count in
                               let r_dif = is_read param dif count in
                               List.append (List.append r_test (List.append r_dit [] )) (List.append r_dif [])
  | Seq'(exp_list) -> List.flatten (List.map (fun a -> is_read param a count) exp_list)
  | Def'(name,value) -> [] (*let r_name = is_read name body count in
                        let r_value= is_read value body count in
                        List.append r_name r_value *)
  | Or'(exp_list) -> List.flatten (List.map (fun a -> is_read param a count) exp_list)
  | LambdaSimple'(params,bodyl) -> let tmp_count = !count in
                                    let param = match param with
                                    |(name,-1, num) -> (name,0,num)
                                    |(name, mj,num) -> (name, (mj +1),num) in
                                    let r_list = is_read param bodyl (inc_count count)  in
                                                          if(List.length r_list <> 0)
                                                              then [tmp_count]
                                                          else []
  | LambdaOpt'(params,opt,bodyl) ->let tmp_count = !count in
                                    let param = match param with
                                    |(name,-1, num) -> (name,0,num)
                                    |(name, mj,num) -> (name, (mj +1),num) in
                                    let r_list = is_read param bodyl (inc_count count)  in
                                                          if(List.length r_list <> 0)
                                                              then [tmp_count]
                                                          else []
  | Applic'(oper,rands) -> let r_oper = is_read param oper count in 
                                        List.append r_oper (List.append (List.flatten (List.map (fun a -> is_read param a count) rands)) [])
  | ApplicTP'(oper,rands) -> let r_oper = is_read param oper count in 
                                        List.append r_oper (List.append (List.flatten (List.map (fun a -> is_read param a count) rands)) [])
  |_->raise X_syntax_error;;

  let rec is_write param body count = match body with
  | Const'(exp)-> []
  | Var'(exp) -> []
  | Set'(Var'(var),exp) -> (check_equ_major param var) @ (is_write param exp count)
  | If'(test,dit,dif) -> let w_test = is_write param test count in
                               let w_dit = is_write param dit count in
                               let w_dif = is_write param dif count in
                               List.append (List.append w_test (List.append w_dit [] )) (List.append w_dif [])
  | Seq'(exp_list) -> List.flatten (List.map (fun a -> is_write param a count) exp_list)
  | Def'(name,value) -> let w_name = is_write param name count in
                                     let w_value= is_write param value count in
                                     List.append w_name (List.append w_value [])
  | Or'(exp_list) -> List.flatten (List.map (fun a -> is_write param a count) exp_list)
  | LambdaSimple'(params,bodyl) ->  let tmp_count = !count in
                                    let param = match param with
                                    |(name,-1, num) -> (name,0,num)
                                    |(name, mj,num) -> (name, (mj +1),num) in
                                    let w_list = is_write param bodyl (inc_count count)  in
                                                          if(List.length w_list <> 0)
                                                              then [tmp_count]
                                                          else []
  | LambdaOpt'(params,opt,bodyl) ->let tmp_count = !count in
                                    let param = match param with
                                    |(name,-1, num) -> (name,0,num)
                                    |(name, mj,num) -> (name, (mj +1),num) in
                                    let w_list = is_write param bodyl (inc_count count)  in
                                                          if(List.length w_list <> 0)
                                                              then [tmp_count]
                                                          else []
  | Applic'(oper,rands) -> let w_oper = is_write param oper count in 
                                        List.append w_oper (List.append (List.flatten (List.map (fun a -> is_write param a count) rands)) [])
  | ApplicTP'(oper,rands) -> let w_oper = is_write param oper count in 
                                        List.append w_oper (List.append (List.flatten (List.map (fun a -> is_write param a count) rands)) [])
  |_->raise X_syntax_error


let make_cartes l1 l2 = List.concat(List.map (fun a -> List.map (fun b -> (a,b)) l2) l1);;

let inner_diff_check cartes = match cartes with
  |(a,b) when a<>b -> true
  |_ -> false;;

let rec check_if_diff cartes_lst = match cartes_lst with
  | [] -> false
  | hd::tl when (inner_diff_check hd) -> true 
  | _::tl -> check_if_diff tl;; 


  let is_needed_box param body= 
   let r_list = is_read (param,-1,0) body (ref 0) in
  let w_list = is_write (param,-1,0) body (ref 0) in
let cartes_lst = make_cartes r_list w_list in
  if((List.length r_list <> 0) && (List.length w_list <> 0) && (check_if_diff cartes_lst))
      then true
  else false;; 

let rec get_index e lst = match lst with
    | [] -> -1
    | h :: t -> if e = h 
                  then 0 
                else 1 + get_index e t;;

let rec box_set_handler expr' lst= match expr' with
  | Const'(exp)-> expr'
  | Var'(exp) -> (match exp with
                | VarParam(name,minor) -> if(List.mem (name,-1) lst)
                                            then BoxGet'(exp)
                                          else expr'
                | VarBound(name,major,minor) -> if(List.mem (name,major) lst)
                                                  then BoxGet'(exp)
                                                else expr'
                |_-> expr')
  | Set'(Var'(var),exp) -> let recur = (box_set_handler exp lst) in
                (match var with
                | VarParam(name,minor) -> if(List.mem (name,-1) lst)
                                            then BoxSet'(var,recur)
                                          else Set'(Var'(var),recur)
                | VarBound(name,major,minor) -> if(List.mem (name,major) lst)
                                                  then BoxSet'(var,recur)
                                                else Set'(Var'(var),recur)
                |_ -> Set'(Var'(var),recur))
  | If'(test,dit,dif) -> let b_test = box_set_handler test lst in
                         let b_dit = box_set_handler dit lst in
                         let b_dif = box_set_handler dif lst in
                         If'(b_test,b_dit,b_dif)
  | Seq'(exp_list) -> Seq'((List.map (fun a -> box_set_handler a lst) exp_list))
  | Def'(name,value) -> Def'(name,(box_set_handler value lst))
  | Or'(exp_list) -> Or'((List.map (fun a -> box_set_handler a lst) exp_list))
  | LambdaSimple'(params,bodyl) ->  let filt_arglst = List.filter (fun a -> is_needed_box a bodyl) params in
                                    let new_arglst = List.map (fun x -> (x, -1)) filt_arglst in 
                                    let new_lst = List.map (fun (x, major) -> (x, (major+1))) lst in
                                    let b_body1 = box_set_handler bodyl (new_arglst @ new_lst) in
                                    let set_lst = List.map (fun a -> Set'(Var'(VarParam(a, (get_index a params))), Box'(VarParam(a, (get_index a params))))) filt_arglst in
                                    let b_body = match b_body1 with 
                                        (*  |Seq'(bodylst) -> Seq'(List.append set_lst [Seq'(bodylst)]) *)
                                          |body when (List.length set_lst) <> 0 -> Seq'(List.append set_lst [b_body1])
                                          |_-> b_body1 in
                                    LambdaSimple'(params,b_body)
  | LambdaOpt'(params,opt,bodyl) -> let new_param_lst = params@[opt] in
                                    let filt_arglst = List.filter (fun a -> is_needed_box a bodyl) new_param_lst in
                                    let new_arglst = List.map (fun x -> (x, -1)) filt_arglst in 
                                    let new_lst = List.map (fun (x, major) -> (x, major+1)) lst in
                                    let b_body1 = box_set_handler bodyl (new_arglst @ new_lst) in
                                    let set_lst = List.map (fun a -> Set'(Var'(VarParam(a, (get_index a new_param_lst))), Box'(VarParam(a, (get_index a new_param_lst))))) filt_arglst in
                                    let b_body = match b_body1 with 
                                       (*   |Seq'(bodylst) -> Seq'(List.append set_lst [Seq'(bodylst)]) *)
                                          |body when (List.length set_lst) <> 0 -> Seq'(List.append set_lst [b_body1])
                                          |_-> b_body1 in
                                    LambdaOpt'(params,opt,b_body)
  | Applic'(oper,rands) -> Applic'((box_set_handler oper lst),List.map (fun a -> box_set_handler a lst) rands)
  | ApplicTP'(oper,rands) -> ApplicTP'((box_set_handler oper lst),List.map (fun a -> box_set_handler a lst) rands)
  |_->raise X_syntax_error;;
  
 module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
 end;;
 
 module Semantics : SEMANTICS = struct
 
 let annotate_lexical_addresses e = lexical_addr_handler e [||];;
 
 let annotate_tail_calls e = tail_calls_handler e false;;
 
 let box_set e = box_set_handler e [];;
 
 let run_semantics expr =
   box_set
      (annotate_tail_calls
        (annotate_lexical_addresses expr)
       ) 
      
;;
   
 end;; (* struct Semantics *)
 
 open Semantics;;
 
