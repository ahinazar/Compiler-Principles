(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "reader.ml";;
 open Reader;;
 
 type constant =
   | Sexpr of sexpr
   | Void
 
 type expr =
   | Const of constant
   | Var of string
   | If of expr * expr * expr
   | Seq of expr list
   | Set of expr * expr
   | Def of expr * expr
   | Or of expr list
   | LambdaSimple of string list * expr
   | LambdaOpt of string list * string * expr
   | Applic of expr * (expr list);;
 
 let rec expr_eq e1 e2 =
   match e1, e2 with
   | Const Void, Const Void -> true
   | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
   | Var(v1), Var(v2) -> String.equal v1 v2
   | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                             (expr_eq th1 th2) &&
                                               (expr_eq el1 el2)
   | (Seq(l1), Seq(l2)
     | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
   | (Set(var1, val1), Set(var2, val2)
     | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                              (expr_eq val1 val2)
   | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr_eq body1 body2)
   | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr_eq body1 body2)
   | Applic(e1, args1), Applic(e2, args2) ->
      (expr_eq e1 e2) &&
        (List.for_all2 expr_eq args1 args2)
   | _ -> false;;
   
                        
 exception X_syntax_error;;


 let reserved_word_list =
   ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "unquote";
    "unquote-splicing"];;  

    let applic_vars =
      ["+","-","/","*"];;

    let rec init_ribs_vars rib_list = match rib_list with
    | Nil -> Nil
    | Pair(Pair (Symbol(expr), value),continiuation) -> Pair (Pair (Symbol(expr), Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)),(init_ribs_vars continiuation))
    | _ -> raise X_syntax_error

    let rec set_ribs_vars rib_list body_exprs= match rib_list with
    | Nil -> Pair (Pair (Symbol "let", Pair (Nil, body_exprs)), Nil)
    | Pair(Pair (Symbol(expr), value),continiuation) -> Pair (Pair (Symbol "set!", Pair (Symbol(expr), value)), (set_ribs_vars continiuation body_exprs))
    | _ -> raise X_syntax_error


  (* work on the tag parser starts here *)
  (*HELPER FUNCTIONS*)
  let rec is_proper_list sexpr = match sexpr with
                       |Nil->true
                       |Pair(first,rest) -> (false || (is_proper_list rest))
                       |_-> false
 
  let rec proper_args_to_list_no_returns (new_list: string list) last_from_list = 
         match last_from_list with
               | Nil-> new_list
               | Pair(Symbol(symbol_expr1),Symbol(symbol_expr2)) 
                     when ((List.mem symbol_expr1 new_list) = false && (List.mem symbol_expr2 new_list) = false && (symbol_expr1 = symbol_expr2) = false) -> 
                           (List.append new_list [symbol_expr1]) 
               | Pair(Symbol(symbol_expr),Nil) 
                     when ((List.mem symbol_expr new_list) = false) -> 
                           (List.append new_list [symbol_expr])
               | Pair(Symbol(symbol_expr),pair_expr)
                     when ((List.mem symbol_expr new_list) = false) ->
                           (proper_args_to_list_no_returns (List.append new_list [symbol_expr]) pair_expr)
               | _ -> raise X_syntax_error;;
 
 
  let rec optional_arg_no_returns (new_list: string list) last_from_list = 
                 match last_from_list with
                       | Pair(Symbol(symbol_expr1),Symbol(symbol_expr2)) 
                             when ((List.mem symbol_expr1 new_list) = false && (List.mem symbol_expr2 new_list) = false && (symbol_expr1 = symbol_expr2) = false) -> 
                                   symbol_expr2 
                       | Pair(Symbol(symbol_expr),pair_expr)
                             when ((List.mem symbol_expr new_list) = false) ->
                                   (optional_arg_no_returns (List.append new_list [symbol_expr]) pair_expr)
                       | _ -> raise X_syntax_error;;
 
  let rec pair_to_list sexpr = match sexpr with
                       |Nil->[]
                       |Pair(first,rest) -> List.append [first] (pair_to_list rest)
                       |_-> [sexpr]
                       
  let rec list_to_pair sexpr = match sexpr with
                       | []->Nil
                       | first::rest -> Pair(first,list_to_pair rest)

(* MACROS *)
         
 let rec quasi_quote_macro sexpr = match sexpr with
 | Pair(Symbol("unquote"), Pair(sexpr, Nil)) -> sexpr (*case 1*)
 | Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)) -> raise X_syntax_error (*case 2*)
 | Nil -> (Pair((Symbol("quote")), (Pair(sexpr, Nil))))  (*case 3*)
 | Symbol _ -> (Pair((Symbol("quote")), (Pair(sexpr, Nil)))) (*case 3*)
 | Vector(sexprs) ->  (*case 4*)
                        let list_of_params = List.map quasi_quote_macro sexprs in
                        let vec_param = (List.fold_right (fun a b -> Pair(a, b)) list_of_params Nil) in 
                        (Pair(Symbol("vector"), vec_param))
 | Pair((Pair((Symbol("unquote-splicing")), (Pair(sexpr, Nil)))), b) ->
       (Pair(Symbol("append"),(Pair(sexpr, (Pair((quasi_quote_macro b), Nil))))))
 | Pair(a, (Pair((Symbol("unquote-splicing")), (Pair(sexpr, Nil))))) ->(Pair((Symbol("cons")), (Pair(quasi_quote_macro a, (Pair(sexpr, Nil))))))
 | Pair(a, b) -> (Pair((Symbol("cons")), (Pair(quasi_quote_macro a, (Pair(quasi_quote_macro b, Nil))))))
 |sexpr-> sexpr;; (*otherwise case*)


  let rec cond_macro rib_list = match rib_list with 
                | Pair(Pair(Symbol("else"),implicit_exprs),Nil)   -> Pair (Symbol "begin" ,implicit_exprs)
                | Pair(Pair(expr1,Pair(Symbol("=>"),Pair(expr2,Nil))),Nil)  -> Pair (Symbol "let",
                                                                    Pair
                                                                     (Pair (Pair (Symbol "value", Pair (expr1, Nil)),
                                                                       Pair
                                                                        (Pair (Symbol "f",
                                                                          Pair (Pair (Symbol "lambda", Pair (Nil, Pair(expr2,Nil))), Nil)),
                                                                        Nil)),
                                                                     Pair
                                                                      (Pair (Symbol "if",
                                                                        Pair (Symbol "value",
                                                                         Pair
                                                                          (Pair (Pair (Symbol "f", Nil),
                                                                            Pair (Symbol "value", Nil)),
                                                                          Nil))),
                                                                      Nil)))
                  | Pair(Pair(expr1,Pair(Symbol("=>"),Pair(expr2,Nil))),rib_list_continuation)  -> Pair (Symbol "let",
                                                                                                           Pair
                                                                                                            (Pair (Pair (Symbol "value", Pair (expr1, Nil)),
                                                                                                              Pair
                                                                                                               (Pair (Symbol "f",
                                                                                                                 Pair (Pair (Symbol "lambda", Pair (Nil, Pair (expr2, Nil))),
                                                                                                                  Nil)),
                                                                                                               Pair
                                                                                                                (Pair (Symbol "rest",
                                                                                                                  Pair
                                                                                                                   (Pair (Symbol "lambda", Pair (Nil, Pair ((cond_macro rib_list_continuation), Nil))),
                                                                                                                   Nil)),
                                                                                                                Nil))),
                                                                                                            Pair
                                                                                                             (Pair (Symbol "if",
                                                                                                               Pair (Symbol "value",
                                                                                                                Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                                                                                                                 Pair (Pair (Symbol "rest", Nil), Nil)))),
                                                                                                             Nil)))
                  | Pair(Pair(test, implicit_expr),Nil)-> Pair(Symbol ("if"),
                                                     Pair( test,
                                                           Pair( Pair (Symbol "begin" ,implicit_expr),
                                                                 Nil)))
                  | Pair(Pair(test, implicit_expr),rib_list_continuation)-> Pair(Symbol ("if"),
                                                     Pair( test,
                                                           Pair( Pair (Symbol "begin" ,implicit_expr),
                                                                 Pair((cond_macro rib_list_continuation),
                                                                       Nil))))
                  | _ -> raise X_syntax_error;;


  let rec let_star_macro continiuation = match continiuation with 
                  | Pair(Nil,body_exprs)  -> Pair(Symbol "let" ,Pair(Nil, body_exprs))
                  | Pair(Pair (rib_expr, Nil),body_exprs)   -> Pair(Symbol "let" ,Pair(Pair (rib_expr, Nil), body_exprs))
                  | Pair(Pair (rib_expr, rib_list),body_exprs)  -> Pair (Symbol "let" , Pair(Pair(rib_expr,Nil) , Pair((let_star_macro (Pair(rib_list,body_exprs))),Nil)))
                  | _ -> raise X_syntax_error;;


(* REC TAG PARSER *)
  let rec tag_parser_not_define_sexpr sexpr= match sexpr with
 (*Constants*)
    | Bool _sexpr -> Const(Sexpr(Bool(_sexpr)))
    | Number _sexpr -> Const(Sexpr(Number(_sexpr)))
    | Char _sexpr -> Const(Sexpr(Char(_sexpr)))
    | String _sexpr -> Const(Sexpr(String(_sexpr)))
    | Nil -> Const(Sexpr(Nil))
    | Pair(Symbol("quote"), Pair (_sexpr, Nil)) -> Const(Sexpr(_sexpr))
 
 (* Quasiquote *)
    | Pair( Symbol("quasiquote"), (Pair(_sexpr, Nil))) -> tag_parser_not_define_sexpr (quasi_quote_macro _sexpr)
 
 (*Variables*)
    | Symbol(_sexpr) when (List.mem _sexpr reserved_word_list = false) -> Var(_sexpr) 

     (*Definitions*)
    | Pair(Symbol("define"), args) when (is_proper_list args = false) -> raise X_syntax_error       
    | Pair(Symbol("define"), Pair (Symbol(var), Pair(expr, Nil))) when (List.mem var reserved_word_list = false) -> Def(Var(var), (tag_parser_not_define_sexpr expr))         
    | Pair(Symbol("define"), Pair(Pair(name, argl), val_expr)) -> tag_parser_not_define_sexpr (Pair(Symbol("define"), Pair(name, Pair( Pair(Symbol("lambda"), Pair(argl, val_expr)) , Nil))))

 (*Conditionals*)
    | Pair(Symbol("if"),Pair(test,Pair(dit,Pair(dif,Nil))))->If((tag_parser_not_define_sexpr test), 
                                                               (tag_parser_not_define_sexpr dit), 
                                                               (tag_parser_not_define_sexpr dif)) 
    | Pair(Symbol("if"), Pair (test,Pair (dit ,Nil)))-> If((tag_parser_not_define_sexpr test),
                                                           (tag_parser_not_define_sexpr dit),
                                                           Const(Void))
    | Pair(Symbol("cond"), rib_list) -> (tag_parser_not_define_sexpr (cond_macro rib_list))
 
 (*Lambda Expressions*)
    | Pair(Symbol("lambda"), Pair (args_list, Nil)) -> raise X_syntax_error
    | Pair(Symbol("lambda"), Pair (Symbol symbol_expr, body_expr_list)) -> LambdaOpt([],   
                                                                           symbol_expr, 
                                                                           (return_seq_if_needed body_expr_list))
    | Pair(Symbol("lambda"), Pair (args_list, body_expr_list)) when ((is_proper_list args_list)=true)-> 
                                                                           LambdaSimple((proper_args_to_list_no_returns [] args_list), 
                                                                           (return_seq_if_needed body_expr_list))
    | Pair(Symbol("lambda"), Pair (args_list, body_expr_list)) when ((is_proper_list args_list)=false)-> 
                                                                           LambdaOpt((proper_args_to_list_no_returns [] args_list),
                                                                           (optional_arg_no_returns [] args_list), 
                                                                            (return_seq_if_needed body_expr_list))
 (*Disjunctions*)
    | Pair (Symbol("or"),Nil)-> Const(Sexpr(Bool(false)))
    | Pair (Symbol("or"), Pair (_sexpr, Nil))-> tag_parser_not_define_sexpr _sexpr
    | Pair (Symbol("or"), rands)  when ((is_proper_list rands)=false) -> raise X_syntax_error 
    | Pair (Symbol("or"), rands)-> Or(List.map tag_parser_not_define_sexpr (pair_to_list rands))
 
 (* And *)
    | Pair((Symbol("and")), params) -> and_macro (pair_to_list params)
 
 (*Assignments*)
    | Pair(Symbol("set!"), Pair (Symbol(symbol_expr), Pair(expr2, Nil))) when (List.mem symbol_expr reserved_word_list = false)-> Set(Var(symbol_expr), (tag_parser_not_define_sexpr expr2)) 
 
 (*Sequences*)
    | Pair(Symbol("begin"),Nil) -> Const(Void)
    | Pair(Symbol("begin"),Pair (Symbol(symbol_expr),Nil)) ->Var(symbol_expr)
    | Pair(Symbol("begin"), Pair(_sexpr, Nil)) -> tag_parser_not_define_sexpr _sexpr
    | Pair(Symbol "begin", _sexpr) when ((is_proper_list _sexpr)=false) -> raise X_syntax_error
    | Pair (Symbol("begin"), exprs)-> Seq(List.map tag_parser_not_define_sexpr (pair_to_list exprs))
    | Pair (Symbol("let"), Pair(param,body))-> let_macro (param,body)
    | Pair(Symbol("let*"), continuation)   ->  tag_parser_not_define_sexpr (let_star_macro continuation)  
    | Pair(Symbol("letrec"), Pair(params,body))   -> tag_parser_not_define_sexpr (let_rec_macro (pair_to_list params) body)

 (*Applications*)
    | Pair(Symbol("+"), Symbol("+")) -> raise X_syntax_error
    | Pair(Symbol("+"), Symbol("-")) -> raise X_syntax_error
    | Pair(Symbol("+"), Symbol("/")) -> raise X_syntax_error
    | Pair(Symbol("+"), Symbol("*")) -> raise X_syntax_error
    | Pair(Symbol("-"), Symbol("+")) -> raise X_syntax_error
    | Pair(Symbol("-"), Symbol("*")) -> raise X_syntax_error
    | Pair(Symbol("-"), Symbol("/")) -> raise X_syntax_error
    | Pair(Symbol("-"), Symbol("-")) -> raise X_syntax_error
    | Pair(Symbol("*"), Symbol("*")) -> raise X_syntax_error
    | Pair(Symbol("*"), Symbol("+")) -> raise X_syntax_error
    | Pair(Symbol("*"), Symbol("-")) -> raise X_syntax_error
    | Pair(Symbol("*"), Symbol("/")) -> raise X_syntax_error
    | Pair(Symbol("/"), Symbol("+")) -> raise X_syntax_error
    | Pair(Symbol("/"), Symbol("/")) -> raise X_syntax_error
    | Pair(Symbol("/"), Symbol("-")) -> raise X_syntax_error
    | Pair(Symbol("/"), Symbol("*")) -> raise X_syntax_error
    | Pair(_,_) when ((is_proper_list sexpr)=false)-> raise X_syntax_error
    | Pair(_, _) -> Applic (tag_parser_not_define_sexpr (List.hd(pair_to_list sexpr)),
                           List.map tag_parser_not_define_sexpr (List.tl(pair_to_list sexpr )))
 (*Otherwise*)
    | _-> raise X_syntax_error


    and return_seq_if_needed sexpr = match sexpr with
            | Nil -> Const(Void)
            | Pair(body_expr, Nil) -> (tag_parser_not_define_sexpr body_expr)
            | Pair(body_expr1, continuation) -> Seq((List.map tag_parser_not_define_sexpr (List.append [body_expr1] (pair_to_list continuation))))
            | _ ->raise X_syntax_error
 
    and and_macro sexpr = match sexpr with
            |[] ->Const(Sexpr(Bool(true)))
            |first :: [] -> tag_parser_not_define_sexpr first
            |first :: rest -> If ((tag_parser_not_define_sexpr first),
                                  (tag_parser_not_define_sexpr (Pair((Symbol("and")), list_to_pair rest))),
                                  Const(Sexpr(Bool(false))))
                       
and let_rec_macro params body =
  let params_name = List.map (fun a -> match a with
        | (Pair(var_name, (Pair(var_val, Nil)))) -> var_name
        | _ -> raise X_syntax_error) params in
  let params_vals = List.map (fun a -> match a with
     | (Pair(var_name, (Pair(var_val, Nil)))) ->var_val
     | _ -> raise X_syntax_error) params in
  let whatever_list = List.map (fun a -> match a with
     | (Pair(var_name, (Pair(var_val, Nil)))) ->
        (Pair(var_name, (Pair(Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil))))
     | _ -> raise X_syntax_error)
     params in
  let body = List.fold_right (fun a s -> Pair(a, s))
                                          (List.map2 (fun var_name var_val -> (Pair((Symbol("set!")),(Pair(var_name, (Pair(var_val, Nil)))))))
                                                            params_name params_vals)
                                          body in
  let params_ret = List.fold_right(fun a s -> Pair(a, s))
                                              whatever_list
                                              Nil in
  Pair(Symbol("let"), (Pair(params_ret, body))) 

(*
and let_rec_macro continiuation = match continiuation with 
                  | Pair(rib_list ,body_exprs)  -> Pair (Symbol "let", Pair((init_ribs_vars rib_list),(set_ribs_vars rib_list body_exprs)))
                  | _ -> raise X_syntax_error *)
                
 and let_macro (param,body)  =
       let variables = List.map (fun a -> match a with
                                               | Pair(a,b)->a
                                               | _-> raise X_syntax_error)
                                              (pair_to_list param) in
       let variables = list_to_pair variables in
       let values = List.map (fun a-> match a with 
                                               | Pair(a, (Pair (b,c))) -> b
                                               | _-> raise X_syntax_error)
                                             (pair_to_list param) in
       let values = List.map tag_parser_not_define_sexpr values in
       Applic((tag_parser_not_define_sexpr (Pair((Symbol "lambda"),(Pair (variables,body))))),values);;

  let rec tag_parser_sexpr sexpr = match sexpr with    
 (*recursive forms*)
    | _ -> (tag_parser_not_define_sexpr sexpr);;
 
 (*####################################*)
 
 module type TAG_PARSER = sig
   val tag_parse_expression : sexpr -> expr
   val tag_parse_expressions : sexpr list -> expr list
 end;; (* signature TAG_PARSER *)
 
 module Tag_Parser : TAG_PARSER = struct

 let tag_parse_expression sexpr = tag_parser_sexpr sexpr;;
 
 let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;
 
   
 end;; (* struct Tag_Parser *)

 open Tag_Parser;;
