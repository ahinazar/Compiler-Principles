#use "semantic-analyser.ml";;
open Semantics;;

let rec make_outer_table table expr = match expr with
  | Const'(Sexpr(exp)) when ((List.mem exp table ) = false)-> table @ [exp]
  | Var' (var) -> table 
  | Box' (var) -> table
  | BoxGet' (var) -> table
  | BoxSet'  (var,exp) ->table @ make_outer_table table exp 
  | If' (test,dit,dif) ->   table @ make_outer_table table test @ make_outer_table table dit @ make_outer_table table dif 
  | Seq'(exp_list) ->table @ List.flatten (List.map (fun a -> make_outer_table table a) exp_list)
  | Or'  (exp_list) -> table @ List.flatten (List.map (fun a -> make_outer_table table a) exp_list)
  | Set'(var,exp) -> table @ make_outer_table table exp 
  | Def' (var,exp) -> table @ make_outer_table table exp 
  | LambdaSimple' (params,body) ->  table @ make_outer_table table body 
  | LambdaOpt' (params,opt,body)-> table @ make_outer_table table body 
  | Applic' (proc,body_exprs) ->table @ make_outer_table table proc @ List.flatten (List.map (fun a -> make_outer_table table a) body_exprs)
  | ApplicTP' (proc,body_exprs) -> table @ make_outer_table table proc @ List.flatten (List.map (fun a -> make_outer_table table a) body_exprs)
  |_->table;;

let rec erase_dups = function
  | [] -> []
  | hd::tl -> [hd] @ (erase_dups (List.filter (fun a -> a<>hd) tl));;

let rec make_inner_table = function
  |[] -> []
  |hd::tl -> (match hd with
                |Bool _  -> (make_inner_table tl) @ [hd]
                |Nil  -> (make_inner_table tl) @ [hd]
                |Number _ -> (make_inner_table tl) @ [hd]
                |Char _ -> (make_inner_table tl) @ [hd]
                |String _ -> (make_inner_table tl) @ [hd]
                |Symbol sym-> [String(sym)]@[hd]@(make_inner_table tl)
                |Pair (head,rest) -> 	let head_sub = (make_inner_table [head]) in 
                                        let rest_sub = (make_inner_table [rest]) in
                                        let tail_sub = (make_inner_table tl) in
                                        head_sub @ rest_sub @ tail_sub @ [hd]
                |Vector (lst) -> (make_inner_table lst) @ (make_inner_table tl) @ [hd]);;

let rec get_offset_const_tbl table exp = match table with
  |[] -> -1
  |hd::tl -> match hd with
                | (sexp,offset,_) when sexp = exp->   offset
                | _ -> get_offset_const_tbl tl exp;;


let rec make_three_tuple table fixed_table offset = match table with
  	| [] -> fixed_table
  	| hd::tl -> match hd with
                | Void -> (make_three_tuple tl ([(Void, 0, "MAKE_VOID")]@fixed_table) (offset+1)) 
                | Sexpr(Nil) -> (make_three_tuple tl (fixed_table@[(Sexpr(Nil), 1, "MAKE_NIL")]) (offset+1))
                | Sexpr(Bool false) -> (make_three_tuple tl (fixed_table@[(Sexpr(Bool false), 2, "MAKE_BOOL(0)")]) (offset+2))
                | Sexpr(Bool true) -> (make_three_tuple tl (fixed_table@[(Sexpr(Bool true), 4, "MAKE_BOOL(1)")]) (offset+2))
                | Sexpr(Number (Int num)) -> (make_three_tuple tl (fixed_table@[(Sexpr(Number(Int num)), offset, "MAKE_LITERAL_INT("^(string_of_int num)^")")]) (offset+9))
                | Sexpr(Number (Float num))-> (make_three_tuple tl (fixed_table@[(Sexpr(Number(Float num)), offset, "MAKE_LITERAL_FLOAT("^(string_of_float num)^")")]) (offset+9))
                | Sexpr(Char ch) -> (make_three_tuple tl (fixed_table@[(Sexpr(Char ch), offset, "MAKE_LITERAL_CHAR("^string_of_int(Char.code ch)^")")]) (offset+2))
                | Sexpr(String str) -> (make_three_tuple tl (fixed_table@[(Sexpr(String str), offset, "MAKE_LITERAL_STRING "^(String.concat "," (List.map (fun x -> (string_of_int (Char.code x))) (string_to_list str)))^"")]) (offset + (String.length str) + 9))
                | Sexpr(Symbol sym) -> (make_three_tuple tl (fixed_table@[(Sexpr(Symbol sym), offset, (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (get_offset_const_tbl fixed_table (Sexpr(String sym)))))]) (offset + 9))
                | Sexpr(Pair (car,cdr)) ->  let car_offset = (get_offset_const_tbl fixed_table (Sexpr(car))) in
                                            let cdr_offset = (get_offset_const_tbl fixed_table (Sexpr(cdr))) in
                                            (make_three_tuple tl (fixed_table@[(Sexpr(Pair(car, cdr)), offset, (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)" car_offset cdr_offset))]) (offset+17))
                | Sexpr(Vector(lst)) -> let vec_addr = List.map (fun a -> (Printf.sprintf "const_tbl+%d" (get_offset_const_tbl fixed_table (Sexpr(a))))) lst in
                                        let vec_addr_str = (String.concat "," vec_addr) in
                                        (make_three_tuple tl (fixed_table@[(Sexpr(Vector(lst)) , offset , "MAKE_LITERAL_VECTOR "^vec_addr_str)]) (offset + ((List.length vec_addr) * 8) + 9));;

let make_consts_tbl_handler asts =
    let table = List.flatten (List.map (fun x-> make_outer_table [] x) asts)  in
    let table = erase_dups table in
    let table = make_inner_table table in
    let table = [Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))]@List.map (fun x -> Sexpr(x)) table in
    let table = erase_dups table in
    let table = make_three_tuple table [] 0 in
    table;;


 let get_const_address consts const = (Printf.sprintf "const_tbl+%d" (get_offset_const_tbl consts const));;


(*##############################################################################*)

let rec get_index_fvar table exp = match table with
  |[] -> -1
  |hd::tl -> match hd with
            | (sexp,offset) when sexp = exp ->   offset
            | _ -> get_index_fvar tl exp;;

let get_addr_fvar fvars_tbl name = 
        let index = get_index_fvar fvars_tbl name in
        "fvar_tbl+" ^ (string_of_int index) ^ " * 8";;

let rec make_names_table expr = match expr with
    | Const'(const) -> []
    | Var'(var) -> (match var with
                    | VarFree(name) -> [name]
                    | _ -> [])
    | Box'(var) -> []
    | BoxGet'(var) -> []
    | BoxSet'(var, exp) -> make_names_table exp
    | If'(test, dit, dif) -> (make_names_table test) @ (make_names_table dit) @ (make_names_table dif)
    | Seq'(exp_list) -> List.flatten (List.map (fun x -> (make_names_table x)) exp_list)
    | Or'(exp_list) -> List.flatten (List.map (fun x -> (make_names_table x)) exp_list)
    | Set'(var,exp) -> (make_names_table var) @ (make_names_table exp)
    | Def'(var,exp) -> (make_names_table var) @ (make_names_table exp)
    | LambdaSimple'(_,body) -> make_names_table body
    | LambdaOpt'(_, _, body) -> make_names_table body
    | Applic'(oper,rands) -> (make_names_table oper) @ (List.flatten (List.map (fun x -> (make_names_table x)) rands))
    | ApplicTP'(oper,rands) ->(make_names_table oper) @ (List.flatten (List.map (fun x -> (make_names_table x)) rands)) ;;

let rec add_addr_fvar_tbl table addr = match table with
    | [] -> []
    | hd::tl -> [(hd,addr)] @ (add_addr_fvar_tbl tl (addr + 1));;
	
let make_fvars_tbl_handler asts = 
    let table = List.flatten (List.map (fun x -> (make_names_table x)) asts) in
    let table = erase_dups table in
    add_addr_fvar_tbl table 0;;

(*##############################################################################*)

let inc_count count = 
  count := !count + 1;
  count;;

let exit_or_ref = (ref 0);;
let else_if_ref = (ref 0);;
let exit_if_ref = (ref 0);;

let lambda_body_ref = (ref 0);;
let lambda_end_ref = (ref 0);;
let lambda_copy_params_ref = (ref 0);;
let lambda_copy_params_finished_ref = (ref 0);;
let lambda_extn_env_finished_ref = (ref 0);;
let lambda_extn_env_ref = (ref 0);;


let lambdaopt_body_ref = (ref 0);;
let lambdaopt_end_ref = (ref 0);;
let lambdaopt_copy_params_ref = (ref 0);;
let lambdaopt_extn_env_ref = (ref 0);;
let lambdaopt_argnum_eq_param_ref = (ref 0);;
let lambdaopt_fixed_frame_ref = (ref 0);;
let lambdaopt_make_arg_list_ref = (ref 0);;
let lambdaopt_extends_and_shift_stack_ref = (ref 0);;
let lambdaopt_descended_and_shift_stack_ref = (ref 0);;
let lambdaopt_extn_env_finished_ref = (ref 0);;
let lambdaopt_shifted_ref = (ref 0);;
let lambdaopt_copy_params_finished_ref = (ref 0);;

let aplictp_override_frame_ref = (ref 0);;

let label_generator label_name counter = label_name ^ (string_of_int(!(inc_count counter)));;

let rec generate_handler consts fvars e mj= match e with
	|Const'(c) -> "mov rax," ^ (get_const_address consts c)
	| Var' (VarParam(_, minor)) ->  "mov rax, qword[rbp + 8 * (4 + "^(string_of_int minor)^")]" 
	| Var'(VarBound(_, major, minor)) -> 	"mov rax, qword [rbp + 8 * 2]"^"\n"^ 
                                                "mov rax, qword [rax + 8 * "^(string_of_int major)^"]"^"\n"^
                                                "mov rax, qword [rax + 8 * "^(string_of_int minor)^"]"
	| Var'(VarFree(v)) -> "mov rax, qword ["^(get_addr_fvar fvars v)^"]"
	| Box' (v) -> 	"MALLOC rdi,8"^"\n"^
                        (generate_handler consts fvars (Var'(v)) mj)^"\n"^
                        "mov [rdi],rax"^"\n"^
                        "mov rax,rdi"^"\n"
	| BoxGet'(v) -> (generate_handler consts fvars (Var'(v)) mj)^"\n"^
                        "mov rax, qword [rax]"^"\n"
	| BoxSet'(v,expr) -> (generate_handler consts fvars expr mj)^"\n"^ 
                            "push rax"^"\n"^
                            (generate_handler consts fvars (Var'(v)) mj)^"\n"^
                            "pop qword [rax]"^"\n"^
                            "mov rax, SOB_VOID_ADDRESS"^"\n"
	| If' (test,dit,dif) -> let lelse_if_label = label_generator "Lelse_if" else_if_ref in
                                let lexit_if_label = label_generator "Lexit_if" exit_if_ref in
                                (generate_handler consts fvars test mj)^"\n"^
                                "cmp rax, SOB_FALSE_ADDRESS"^"\n"^
                                "je "^lelse_if_label^"\n"^
                                (generate_handler consts fvars dit mj)^"\n"^
                                "jmp "^lexit_if_label^"\n"^
                                lelse_if_label^":"^"\n"^
                                (generate_handler consts fvars dif mj)^"\n"^
                                lexit_if_label^":"
	| Seq'(exp_list) -> let lst_str = List.map (fun x -> (generate_handler consts fvars x mj)) exp_list in
                            (String.concat "\n" lst_str)
	| Or'  (exp_list) -> let lexit_or_label = label_generator "Lexit_or" exit_or_ref in
                             let lst_str = List.map (fun x -> (generate_handler consts fvars x mj)) exp_list in
                             let str_concat = "\n"^"cmp rax, SOB_FALSE_ADDRESS"^"\n"^"jne "^lexit_or_label^"\n" in
                             let str_not_final = (String.concat str_concat lst_str) in
                             str_not_final^"\n"^lexit_or_label^":"
	| Set'(Var'(VarParam(_, minor)),expr) -> (generate_handler consts fvars expr mj)^"\n"^ 
                                                 "mov qword [rbp + 8 * (4 + "^(string_of_int minor)^")], rax"^"\n"^
                                                 "mov rax, SOB_VOID_ADDRESS"
	| Set'(Var'(VarBound(_,major,minor)),expr) ->	(generate_handler consts fvars expr mj)^"\n"^ 
                                                        "mov rbx, qword [rbp + 8 * 2]"^"\n"^
                                                        "mov rbx, qword [rbx + 8 * "^(string_of_int major)^"]"^"\n"^
                                                        "mov qword [rbx + 8 * "^(string_of_int minor)^"], rax"^"\n"^
                                                        "mov rax, SOB_VOID_ADDRESS"
	| Set'(Var'(VarFree(v)),expr) -> (generate_handler consts fvars expr mj)^"\n"^  
                                         "mov qword ["^(get_addr_fvar fvars v)^"], rax"^"\n"^
                                         "mov rax, SOB_VOID_ADDRESS"
	| Def'(Var'(VarFree(v)),expr) -> (generate_handler consts fvars expr mj)^"\n"^ 
                                         "mov qword ["^(get_addr_fvar fvars v)^"], rax"^"\n"^
                                         "mov rax, SOB_VOID_ADDRESS"
	| LambdaSimple' (params,body) ->let lambda_body = label_generator "lambda_body" lambda_body_ref in   
                                        let lambda_end = label_generator "lambda_end" lambda_end_ref in  
                                        let lambda_copy_params = label_generator "lambda_copy_params" lambda_copy_params_ref in
                                        let lambda_extn_env_finished = label_generator "lambda_extn_env_finished" lambda_extn_env_finished_ref in
                                        let lambda_copy_params_finished = label_generator "lambda_copy_params_finished" lambda_copy_params_finished_ref in
                                        let lambda_extn_env = label_generator "lambda_extn_env" lambda_extn_env_ref in

                                        "MALLOC rbx, "^(string_of_int ((mj + 1) *8))^"			; rbx <- ExtEnv\n"^
									
                                        (*COPYS ENV TO EXTENV - ExtEnv[i+1] <- Env[i]; *)
                                        "mov rcx, "^(string_of_int mj)^"\n"^      		(* rcx <- |Env| *)
                                        "mov r8, rcx"^"\n"^
                                        "mov r10, qword [rbp + 8 * 2]"^"\n"^     		(* r10 <- Env *)
                                        "cmp r8,0"^"\n"^
                                        "je "^lambda_extn_env_finished^"\n"^
                                        lambda_extn_env^":"^"\n"^
                                        "	mov r11, qword[r10 + 8 * (rcx - 1)]"^"\n"^        (* r11<-Env[i] *) 
                                        "	mov qword[rbx + 8 * rcx],r11"^"\n"^               (* ExtEnv[i+1]<- Env[i] *)  
                                        "	loop "^lambda_extn_env^"\n"^
                                        lambda_extn_env_finished^":"^"\n"^
                                        (* CREATES PARAMS ARRAY*)  
                                        "mov r8, qword [rbp + 8 * 3]"^"\n"^ 				(* arg number *)
                                        "mov r9, r8"^"\n"^
                                        "shl r9, 3"^"\n"^
                                        "MALLOC r9, r9"^"			; r9 <- ENVTOEXT\n"^ 	(*ALLOCATE*)
                                        "mov rcx, r8"^"\n"^ 								(* rcx <- arg number *)
                                        "cmp r8, 0"^"\n"^ 
                                        "je "^lambda_copy_params_finished^"\n"^								
                                        lambda_copy_params^":"^"\n"^
                                        "	mov r14, PVAR(rcx-1)"^"\n"^ 
                                        "	mov [r9 + 8 * (rcx-1)], r14"^"\n"^        		(* r9<-param[i] *) 
                                        "	loop "^lambda_copy_params^"\n"^
                                        lambda_copy_params_finished^":"^"\n"^					(*ADDING THE NEW ENV TO EXT-ENV*)
                                        "mov qword[rbx],r9"^"\n"^
                                        (*CREATES CLOSURE*)
                                        "MAKE_CLOSURE(rax, rbx, "^lambda_body^ ")" ^ "\n\n" ^ 
                                        "jmp "^lambda_end^ "\n\n" ^
                                        lambda_body^":"^"\n"^
                                        "	push rbp"^"\n"^
                                        "	mov rbp, rsp"^"\n	"^ 		
                                        (generate_handler consts fvars body (mj+1))^"\n"^
                                        "	leave"^"\n"^
                                        "	ret"^"\n"^
                                        lambda_end^":"^"\n" 
	| LambdaOpt' (params,opt,body)->let lambdaopt_body = label_generator "lambdaopt_body" lambdaopt_body_ref in   
                                        let lambdaopt_end = label_generator "lambdaopt_end" lambdaopt_end_ref in  
                                        let lambdaopt_extn_env = label_generator "lambdaopt_extn_env" lambdaopt_extn_env_ref in
                                        let lambdaopt_copy_params = label_generator "lambdaopt_copy_params" lambdaopt_copy_params_ref in
                                        let lambdaopt_extn_env_finished = label_generator "lambdaopt_extn_env_finished" lambdaopt_extn_env_finished_ref in
                                        let lambdaopt_argnum_eq_param = label_generator "lambdaopt_argnum_eq_param" lambdaopt_argnum_eq_param_ref in
                                        let lambdaopt_fixed_frame = label_generator "lambdaopt_fixed_frame" lambdaopt_fixed_frame_ref in
                                        let lambdaopt_make_arg_list = label_generator "lambdaopt_make_arg_list" lambdaopt_make_arg_list_ref in
                                        let lambdaopt_extends_and_shift_stack = label_generator "lambdaopt_extends_and_shift_stack" lambdaopt_extends_and_shift_stack_ref in
                                        let lambdaopt_descended_and_shift_stack = label_generator "lambdaopt_descended_and_shift_stack" lambdaopt_descended_and_shift_stack_ref in
                                        let lambdaopt_shifted = label_generator "lambdaopt_shifted" lambdaopt_shifted_ref in
                                        let lambdaopt_copy_params_finished = label_generator "lambdaopt_copy_params_finished" lambdaopt_copy_params_finished_ref in
									
                                        "MALLOC rbx, "^(string_of_int ((mj + 1) *8))^"			; rbx <- ExtEnv\n"^
                                        (*COPYS ENV TO EXTENV - ExtEnv[i+1] <- Env[i]; *)
                                        "mov rcx, "^(string_of_int mj)^"\n"^      		(* rcx <- |Env| *)
                                        "mov r8, rcx"^"\n"^
                                        "mov r10, qword [rbp + 8 * 2]"^"\n"^     		(* r10 <- Env *)
                                        "cmp r8,0"^"\n"^
                                        "je "^lambdaopt_extn_env_finished^"\n"^
                                        lambdaopt_extn_env^":"^"\n"^
                                        "	mov r11, qword[r10 + 8 * (rcx - 1)]"^"\n"^        (* r11<-Env[i] *) 
                                        "	mov qword[rbx + 8 * rcx],r11"^"\n"^               (* ExtEnv[i+1]<- Env[i] *)  
                                        "	loop "^lambdaopt_extn_env^"\n"^
                                        lambdaopt_extn_env_finished^":"^"\n"^
                                        (* CREATES PARAMS ARRAY*)  
                                        "mov r8, qword [rbp + 8 * 3]"^"\n"^ 				(* arg number *)
                                        "mov r9, r8"^"\n"^
                                        "shl r9, 3"^"\n"^
                                        "MALLOC r9, r9"^"			; r9 <- ENVTOEXT\n"^ 	(*ALLOCATE*)
                                        "mov rcx, r8"^"\n"^ 								(* rcx <- arg number *)
                                        "cmp r8, 0"^"\n"^ 
                                        "je "^lambdaopt_copy_params_finished^"\n"^								
                                        lambdaopt_copy_params^":"^"\n"^
                                        "	mov r14, PVAR(rcx-1)"^"\n"^ 
                                        "	mov [r9 + 8 * (rcx-1)], r14"^"\n"^        		(* r9<-param[i] *) 
                                        "	loop "^lambdaopt_copy_params^"\n"^
                                        lambdaopt_copy_params_finished^":"^"\n"^					(*ADDING THE NEW ENV TO EXT-ENV*)
                                        "mov qword[rbx],r9"^"\n"^
                                        (*CREATES CLOSURE*)
                                        "MAKE_CLOSURE(rax, rbx, "^lambdaopt_body^ ")" ^ "\n\n" ^ 
                                        "jmp "^lambdaopt_end^ "\n\n" ^
                                        lambdaopt_body^":"^"\n"^
                                        (*###########################################################################*)
                                        "mov r8, [rsp + 2 * 8]"^"\n"^ (*argnum*)
                                        "cmp r8, "^(string_of_int (List.length params))^"\n"^ (*if argnum < |param|*)
                                        "jl 0xbad"^"\n"^ (*not enough args to proc*)

                                        "mov r8, [rsp + 2 * 8]"^"\n"^ (*argnum*)
                                        "cmp r8, "^(string_of_int (List.length params))^"\n"^	(*if argnum = |param|*)
                                        "je "^lambdaopt_argnum_eq_param^"\n"^
                                        (*HERE:	################### argnum > |param| #########################*)
                                        (*make some list*)
                                        "mov rcx, [rsp + 2*8]"^"\n"^ (*argnum*)
                                        "add rcx, -"^(string_of_int (List.length params))^"\n"^
                                        "mov r9,SOB_NIL_ADDRESS"^"\n"^
                                        lambdaopt_make_arg_list^":"^"\n"^
                                        "	mov r8, [rsp + 2*8 + (rcx+"^(string_of_int (List.length params))^")*8]"^"\n"^
                                        "	MAKE_PAIR(rsi, r8, r9)"^"\n"^
                                        "	mov r9, rsi"^"\n"^
                                        "loop "^lambdaopt_make_arg_list^"\n"^
                                        "mov rsi, r9"^"\n"^

                                        (*shift stack by argnum-|param|-1*)
                                        "mov rcx, [rsp+2*8]"^"\n"^
                                        "add rcx, -"^(string_of_int ((List.length params)+1))^"\n"^ (*rcx <- argnum -|params| - 1*)
                                        "mov r9, rcx"^"\n"^
                                        "cmp r9, 0 "^"\n"^ (*if (argnum -|params| - 1) = 0 then no need to shift*)
                                        "je "^lambdaopt_shifted^"\n"^
                                        "mov r10, rcx"^"\n"^

                                        "mov rcx, [rsp+2*8]"^"\n"^
                                        "add rcx, 3"^"\n"^
                                        "sub rcx, r10"^"\n"^
                                        "mov r9, [rsp+2*8]"^"\n"^
                                        lambdaopt_descended_and_shift_stack^":"^"\n"^
                                        "	mov r8, [rsp + 8*2 + (rcx-3)*8]"^"\n"^
                                        "	mov qword[rsp + 8*2 + r9*8], r8"^"\n"^ (*addr of last arg at first time*)
                                        "	dec r9"^"\n"^
                                        "	loop "^lambdaopt_descended_and_shift_stack^"\n"^
                                        "shl r10, 3"^"\n"^
                                        "add rsp, r10"^"\n"^ (*correct rsp to new start*)

                                        (*argnum<-|param|+1*)(*put list above*)
                                        lambdaopt_shifted^":"^"\n"^
                                        "mov qword[rsp+2*8], "^(string_of_int ((List.length params)+1))^"\n"^
                                        "mov qword[rsp+2*8+ "^(string_of_int ((List.length params)+1))^"*8],rsi"^"\n"^
                                        "jmp "^lambdaopt_fixed_frame^"\n"^
                                        lambdaopt_argnum_eq_param^":\n"^
                                        (*HERE:	################### argnum = |param| #########################*)
                                        (*shift stack by -1*)
                                        "mov rcx, "^(string_of_int ((List.length params)))^"\n"^
                                        "add rcx, 3"^"\n"^
                                        "mov r9, 0"^"\n"^
                                        lambdaopt_extends_and_shift_stack^":"^"\n"^
                                        "	mov r8, [rsp + 8*r9]"^"\n"^
                                        "	mov qword[rsp + 8*(r9-1)], r8"^"\n"^
                                        "	inc r9"^"\n"^
                                        "	loop "^lambdaopt_extends_and_shift_stack^"\n"^
                                        (*argnum<-|param|+1*)(*put empty list above*)
                                        "add rsp, -8"^"\n"^ (*correct rsp to new start*)
                                        "mov qword[rsp+2*8], "^(string_of_int ((List.length params)+1))^"\n"^
                                        "mov qword[rsp + 2*8 + "^(string_of_int ((List.length params)+1))^"*8],SOB_NIL_ADDRESS"^"\n"^
                                        lambdaopt_fixed_frame^":\n"^
                                        (*###########################################################################*)
                                        "	push rbp" ^ "\n" ^ 
                                        "	mov rbp, rsp" ^ "\n" ^ 		
                                        (generate_handler consts fvars body (mj+1))  ^ "\n" ^  
                                        "	leave" ^ "\n" ^ 
                                        "	ret" ^ "\n\n" ^
                                        lambdaopt_end ^ ":" ^ "\n\n"

	| Applic' (oper,rands) ->	let rands_rev = List.rev rands in
                                        let rands_eval = (List.map (fun a -> (generate_handler consts fvars a mj)^"\npush rax\n") rands_rev) in
                                        let rands_to_push = (String.concat ""  rands_eval) in
                                        let args_number = (string_of_int (List.length rands)) in
                                        let oper_rec = generate_handler consts fvars oper mj in
                                        rands_to_push^"\n"^
                                        "push "^args_number^"\n"^
                                        oper_rec^"\n"^
                                        "cmp byte[rax],T_CLOSURE"^"\n"^
                                        "jne 0xbad"^"\n"^
                                        "CLOSURE_ENV rdi,rax"^"\n"^
                                        "push rdi"^"\n"^
                                        "CLOSURE_CODE rdi,rax"^"\n"^
                                        "call rdi"^"\n"^
                                        "add rsp , 8*1 "^"\n"^
                                        "pop rbx ; pop arg count"^"\n"^
                                        "shl rbx , 3 "^"\n"^
                                        "add rsp , rbx"^"\n"
								  

	| ApplicTP' (oper,rands) ->	let rands_rev = List.rev rands in
                                        let rands_eval = (List.map (fun a -> (generate_handler consts fvars a mj)^"\npush rax\n") rands_rev) in
                                        let rands_to_push = (String.concat ""  rands_eval) in
                                        let args_number = (string_of_int (List.length rands)) in
                                        let oper_rec = generate_handler consts fvars oper mj in
                                        let aplictp_override_frame = label_generator "aplictp_override_frame" aplictp_override_frame_ref in 
                                        rands_to_push^"\n"^
                                        "push "^args_number^"\n"^
                                        oper_rec^"\n"^
                                        "cmp byte[rax],T_CLOSURE"^"\n"^
                                        "jne 0xbad"^"\n"^
                                        "CLOSURE_ENV rdi,rax"^"\n"^
                                        "push rdi"^"\n"^
                                        "push qword [rbp + 8 * 1] ; old ret addr"^"\n"^
                                        ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"^
                                        (*FIX THE STACK - OVERRIDE THE PREV FRAME starts from rsp*)
                                        "mov r13, [rbp]					  ;r13 <- old_rbp
                                        mov r14, [rbp+3*8]                  ;r14 <- old args num
                                        add r14, 3
                                        shl r14, 3
                                        add r14, rbp                        ; r14 <- old frame last arg address =  [rbp + 3 * 8 + old_arg_num * 8]
                                        mov rcx, [rsp+2*8]                  ; new arg number 
                                        add rcx, 3                          ; for arg num , env, return addr

                                        "^aplictp_override_frame^":
                                        mov r8, [rsp+(2+rcx-3)*8]
                                        mov [r14], r8
                                        sub r14, 8
                                        loop "^aplictp_override_frame^"

                                        mov rbp, r13                        ;r13 hold old_rbp
                                        add r14,8
                                        mov rsp, r14
                                        ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
                                        CLOSURE_CODE rdi,rax
                                        jmp rdi"^"\n"
	| a-> ""

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * int * string) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * int * string) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = make_consts_tbl_handler asts;;
  let make_fvars_tbl asts = make_fvars_tbl_handler asts;;
  let generate consts fvars e = generate_handler consts fvars e 0;;
end;;

open Code_Gen;;
