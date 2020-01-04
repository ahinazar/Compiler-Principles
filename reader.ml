
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;


module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(*Symbol parser*)
    let _symbol_char_ = one_of "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!$^*-_=+<>?/:";; 
    let _symbol_without_check_for_hashtag_dot_ = pack (plus _symbol_char_) (fun (sym) -> Symbol(String.lowercase_ascii(list_to_string(sym))));;
  let _symbol_ = pack (not_followed_by _symbol_without_check_for_hashtag_dot_ (one_of ".#")) (fun a -> a);;

(* Boolean parser *)
    let _t_bool_ = pack (caten (char '#') (char_ci 't')) (fun (a,b) -> Bool true);;
    let _f_bool_ = pack (caten (char '#') (char_ci 'f')) (fun (a,b)-> Bool false);;
    let _bool_without_check_for_symbol_ = pack (disj _t_bool_ _f_bool_) ((fun a -> a));;
    let _plus_bool_ = plus _bool_without_check_for_symbol_;;
    (* removed '#' from _not_followed_by_bool_beacuse if its exists -> #t#t=> no_match *)
  let _bool_ =  pack (not_followed_by _bool_without_check_for_symbol_ _symbol_char_) (fun a -> a);;

(* Number parsers: *)
    (* Hex digit parser *)
        let _digit_ =range '0' '9';;
        let _non_capital_hex_letter_ = range 'a' 'f';;
        let _capital_hex_letter_ = range 'A' 'F';;
      let _hex_digit_ = disj_list [_digit_;_non_capital_hex_letter_;_capital_hex_letter_];;
    (* Hex Prefix parser *)
      let _hex_prefix_ = caten (char '#') (char_ci 'x');;
    (*Number parser*)
      let _natural_number_ = plus(_digit_);;
    (*Integer parser*)
        let _int_natural_number_  = pack (_natural_number_) (fun lst ->  (int_of_string (list_to_string lst)));;
        let _plus_minus_ = maybe (disj (char '+') (char '-'));;
        let _natural_with_sign_= caten _plus_minus_ _int_natural_number_;;
        let _integer_before_pack_ = pack _natural_with_sign_ 
                                          (fun (sign, num)-> match sign with 
                                                              | Some ('-') -> -num 
                                                              | _-> num);;
      let _integer_ = pack _integer_before_pack_ (fun (a)-> Int(a));;
    (*Float parser*)
        let _natural_string_with_dot_ = pack (caten (_natural_number_) (char '.')) (fun (a,b)-> (String.concat "" [(list_to_string a);"."]));;
        let _float_string_= pack (caten _natural_string_with_dot_ _natural_number_) (fun (a,b)->(String.concat "" [a;(list_to_string b)]));;
        (*let _unsigned_float_ = pack (disj _float_string_ _natural_string_with_dot_) (fun a -> (float_of_string a));;*)
        let _unsigned_float_ = pack _float_string_ (fun a -> (float_of_string a));;
        let _float_with_sign_= caten _plus_minus_ _unsigned_float_;;
        let _float_before_pack_ = pack _float_with_sign_ 
                                        (fun (sign, num)-> match sign with 
                                                            | Some ('-') -> (-1.0) *. num 
                                                            | _-> num);;
      let _float_ = pack _float_before_pack_ (fun (a)-> Float(a));;
    (*Hex Natural Number praser*)
      let _hex_natural_number_ = plus(_hex_digit_);;
    (*Hex Integer parser*)
        let _hex_int_natural_number_  = pack (_hex_natural_number_) (fun lst ->  (int_of_string (list_to_string ('0'::'x'::lst))));;
        let _hex_natural_with_sign_=pack (caten _hex_prefix_ (caten _plus_minus_ _hex_int_natural_number_)) (fun (a,b)->b);;
      let hex_integer = pack _hex_natural_with_sign_ 
                              (fun (sign, num)-> match sign with 
                                                  | Some ('-') -> Int(-num) 
                                                  | _-> Int(num));;
    (*Hex Float parser*)
        let _hex_natural_string_with_dot_ = pack (caten (_hex_natural_number_) (char '.')) (fun (a,b)-> (String.concat "" [(list_to_string ('0'::'x'::a));"."]));;
        let _hex_float_string_= pack (caten _hex_natural_string_with_dot_ _hex_natural_number_) (fun (a,b)->(String.concat "" [a;(list_to_string b)]));;
        let _hex_unsigned_float_ = pack _hex_float_string_ (fun a -> (float_of_string a));;
        let _hex_float_with_sign_= pack (caten _hex_prefix_ (caten _plus_minus_ _hex_unsigned_float_)) (fun (a,b)->b);;
      let hex_float = pack _hex_float_with_sign_ 
                            (fun (sign, num)-> match sign with 
                                                | Some ('-') -> Float((-1.0) *. num) 
                                                | _-> Float(num));;
    (*Scientific notation*)
        let _scientific_digits_ = one_of "0123456789+-";;
        let _e_sign_and_pow_string_ = pack (caten (char_ci 'e') _integer_before_pack_) (fun (a,b)-> (a::(string_to_list(string_of_int(b)))));;
        let _scientific_float_ = pack (caten _float_before_pack_ _e_sign_and_pow_string_)
                                  (fun (a,b)-> Float(float_of_string (String.concat "" [(string_of_float a);(list_to_string b)])));;
        let _scientific_integer_ = pack (caten _integer_before_pack_ _e_sign_and_pow_string_)
                                  (fun (a,b)-> Float(float_of_string (String.concat "" [(string_of_int a);(list_to_string b)])));;
      let _scientific_notation_ = pack (disj _scientific_float_ _scientific_integer_) (fun a->a);;
    let _number_without_check_for_symbol_ = pack (disj_list [_scientific_notation_;hex_float;_float_;hex_integer;_integer_]) (fun a-> Number(a));;
    let _number_ = pack (not_followed_by _number_without_check_for_symbol_ (diff _symbol_char_ _scientific_digits_)) (fun a -> a);;

(* Char parser: *)
    (*Char prefix parser*)
      let _char_prefix_ = caten (char '#') (char '\\');;
    (* Visible simple char parser*)
      let _visible_simple_char_ = guard nt_any (fun ch->'!' <= ch);;
      (*Hex char praser*)
      let _hex_char_one_digits_ = pack (caten (char_ci 'x') _hex_digit_)
                          (fun (a,b)-> (char_of_int (int_of_string (list_to_string ('0'::'x'::[b])))));;

                          let _hex_char_two_digits_ = pack (caten (char_ci 'x') (guard  (caten _hex_digit_ _hex_digit_) 
                          (fun (a,b)->
                         (a>='0' && a<='7') && ((b>='0' && b<='9') 
                                      || (b>= 'a' && b<='f') 
                                      || (b>= 'A' && b<='F'))))) 
(fun (a,(b,c))-> (char_of_int (int_of_string (list_to_string ('0'::'x'::b::[c])))));;
      
    (*Named char parser*)
        let _named_newline_=pack (word_ci "newline") (fun b-> '\n');;
        let _named_nul_= pack (word_ci "nul") (fun b-> char_of_int 0);;
        let _named_page_= pack (word_ci "page") (fun b-> char_of_int 12);;
        let _named_return_= pack (word_ci "return") (fun b-> '\r');;
        let _named_space_= pack (word_ci "space") (fun b-> ' ');;
        let _named_tab_= pack (word_ci "tab") (fun b-> '\t');;
      let _named_char_ = disj_list [_named_nul_;_named_newline_;_named_page_;_named_return_;_named_space_;_named_tab_];;
    let _after_prefix_ = disj_list [_hex_char_two_digits_;_hex_char_one_digits_;_named_char_;_visible_simple_char_];;
    let _char_ = pack (caten _char_prefix_ _after_prefix_) (fun (a,b) -> Char b);;

(* String parser *)
  let _quote_ = pack (word "\"") (fun lst -> '\"');;
    (*String Literal Char parser *)
      let _string_literal_char_ = pack (guard nt_any (fun ch -> '\\' <> ch && '\"' <> ch)) (fun ch -> ch);;
    (* String meta char parser *)
        let _slash_r_ = pack (word "\\r") (fun lst -> '\r');;
        let _slash_quote_ = pack (word "\\\"") (fun lst -> '\"');;
        let _slash_t_ = pack (word "\\t") (fun lst -> '\t');;
        let _slash_f_ = pack (word "\\f") (fun lst -> (Char.chr 12));;
        let _slash_n_ = pack (word "\\n") (fun lst -> '\n');;
        let _slash_slash_ = pack (word "\\\\") (fun lst -> '\\');;
      let _string_meta_char_ = disj_list [_slash_r_; _slash_quote_; _slash_t_;_slash_f_;_slash_n_;_slash_slash_];; 
  
    (* String hex char parser *)
    let _no_semicolon_string_hex_char_one_digit_ = pack (caten (caten (char '\\') (char_ci 'x'))  _hex_digit_) 
    (fun ((slash,x),hexDig) -> (char_of_int (int_of_string (list_to_string ('0'::'x'::[hexDig])))));;
    
let _no_semicolon_string_hex_char_two_digits_ = pack (caten (caten (char '\\') (char_ci 'x'))  (caten _hex_digit_ _hex_digit_)) 
    (fun ((slash,x),(first,second)) -> (char_of_int (int_of_string (list_to_string ('0'::'x'::first::[second])))));;
    
let _disj_hex_chars_ = disj  _no_semicolon_string_hex_char_two_digits_ _no_semicolon_string_hex_char_one_digit_

let _string_hex_char_ = pack (caten _disj_hex_chars_ (char ';')) (fun (a,b) -> a);;

    (* String Char parser *)
      let _string_char_ = (disj_list [_string_meta_char_;_string_hex_char_;_string_literal_char_]);;
    let _star_string_char = (star _string_char_);;
    let _string_ = pack (caten (caten _quote_ (star _string_char_)) _quote_) 
                        (fun ((lquote,stringChar),rquote) -> String(list_to_string stringChar));; 

      
        
let _fixed_sograim_ = disj (char '(') (char '[');;
                        
(*Sexpr parser*)
let rec _Sexpr_ s = 
    let _packed_ = pack (disj_list [_bool_spaces_;_char_spaces_;_number_spaces_;_string_spaces_;_symbol_spaces_
                                    ;_list_squered_spaces_;_list_rounded_spaces_; _dotted_list_squered_spaces_
                                    ;_dotted_list_rounded_spaces_;_vector_rounded_spaces_
                                    ; _quoted_spaces_;_quasi_quoted_spaces_;_unquoted_spaces_;_unquote_and_spliced_spaces_;_three_dots_spaces_;_nil_spaces_]) 
                        (fun (list)->list) in 
    _packed_ s
  (*space parser*)
    and _space_ s= 
      let _packed_ = pack (guard nt_any (fun a->a<=' ')) (fun c->c) in
      _packed_ s
  (*List parser*)
    and _list_squered_ s = 
      let _packed_ = pack (caten (caten (char '[') (star _Sexpr_)) (char ']')) 
                          (fun ((lparen,arg_sexpr_list),rparen)-> List.fold_right(fun n1 n2 -> Pair(n1,n2)) 
                          arg_sexpr_list 
                          Nil) in
      _packed_ s
    and _list_rounded_ s = 
      let _packed_ = pack (caten (caten (char '(') (star _Sexpr_)) (char ')')) 
                          (fun ((lparen,arg_sexpr_list),rparen)-> List.fold_right (fun n1 n2 -> Pair(n1,n2)) 
                          arg_sexpr_list 
                          Nil) in
      _packed_ s

  (*DottedList parser*)
    and _dotted_list_rounded_ s = 
      let _packed_ = pack (caten (caten (caten (caten (char '(') (plus _Sexpr_)) (char '.')) _Sexpr_) (char ')')) 
                          (fun ((((_lparen_,_plus_sexpr_),_dot_),_Sexpr_),_rparen_)-> List.fold_right(fun n1 n2 -> Pair(n1,n2)) 
                          _plus_sexpr_ 
                          _Sexpr_) in
      _packed_ s
    and _dotted_list_squered_ s = 
      let _packed_ = pack (caten (caten (caten (caten (char '[') (plus _Sexpr_)) (char '.')) _Sexpr_) (char ']')) 
                          (fun ((((_lparen_,_plus_sexpr_),_dot_),_Sexpr_),_rparen_)-> List.fold_right (fun n1 n2 -> Pair(n1,n2)) 
                          _plus_sexpr_ 
                          _Sexpr_) in
      _packed_ s

  (*Vector parser*)
    and _vector_rounded_ s = 
      let _packed_ = pack (caten (caten (word "#(") (star _Sexpr_)) (char ')')) 
                          (fun ((_sulamit_lparen_,arg_sexpr_list),rparen)-> Vector(arg_sexpr_list)) in
      _packed_ s
    and _vector_squered_ s = 
      let _packed_ = pack (caten (caten (word "#[") (star _Sexpr_)) (char ']')) 
                          (fun ((_sulamit_lparen_,arg_sexpr_list),rparen)-> Vector(arg_sexpr_list)) in
      _packed_ s

  (*Quoted parser*)
    and _quoted_ s = 
      let _packed_ = pack (caten (char '\'') _Sexpr_) 
                          (fun (quate,sexpr_arg) -> Pair (Symbol("quote"), Pair(sexpr_arg , Nil))) in
      _packed_ s
    and _quasi_quoted_ s = 
      let _packed_ = pack (caten (char '`') _Sexpr_) 
                          (fun (quasi_quate, sexpr_arg)->Pair (Symbol("quasiquote"), Pair(sexpr_arg , Nil))) in
      _packed_ s
    and _unquoted_ s = 
      let _packed_ = pack (caten (char ',') _Sexpr_) 
                          (fun (unquoted, sexpr_arg)->Pair (Symbol("unquote"), Pair(sexpr_arg , Nil))) in
      _packed_ s
    and _unquote_and_spliced_ s = 
      let _packed_ = pack (caten (caten (char ',') (char '@')) _Sexpr_) 
                          (fun ((unquote_splicing,shtrodel), sexpr_arg)->Pair (Symbol("unquote-splicing"), Pair(sexpr_arg , Nil))) in
      _packed_ s

  (*comment parser*)
    and _any_char_except_backslash_n_ s= 
      let _packed_ = pack (guard nt_any (fun c->c<>'\n')) (fun c -> c) in
      _packed_ s
    and _semi_colon_ s= 
      let _packed_ = pack (char ';') (fun c -> c) in
      _packed_ s
    and _backslash_n_ s= 
      let _packed_ =pack (char '\n') (fun c -> c) in
      _packed_ s
    and _backslash_n_or_end_of_input_ s= 
      let _packed_ = pack (disj_list [_backslash_n_;char (char_of_int 4); char (char_of_int 3)]) (fun c -> c) in
      _packed_ s
    and _line_comment_ s= 
      let _packed_ = pack (caten (caten _semi_colon_ (star _any_char_except_backslash_n_)) _backslash_n_or_end_of_input_) 
                          (fun ((a,b),c)-> ' ') in
      _packed_ s
    and _sulamit_semicolon_ s= 
      let _packed_ = pack (word "#;") (fun c -> c) in
      _packed_ s
    and _sexpr_comment_ s= 
      let _packed_ = pack (caten _sulamit_semicolon_ _Sexpr_) (fun (a,b)-> ' ') in
      _packed_ s

  (*skip parser*)
    and _skip_star_ s= 
      let _packed_ = pack (star (disj_list [_space_;_line_comment_;_sexpr_comment_])) 
                          (fun c->c) in
      _packed_ s

      
      
      
  (*make general parser*)
    and make_nt_parser p s= 
      let _packed_ = pack (caten (caten _skip_star_  p) _skip_star_) 
                          (fun ((a,b),c)->b) in
      _packed_ s
      
      and _nil_ s= 
      let _packed_ = pack (caten (caten (char '(') _skip_star_) (char ')')) (fun ((a,b),c)->Nil) in
      _packed_ s


  (* spaces parsers: *)
    and _bool_spaces_ s= 
      let _packed_ = pack (make_nt_parser _bool_) (fun c ->c)in
      _packed_ s
    and _char_spaces_ s= 
      let _packed_ = pack (make_nt_parser _char_) (fun c ->c)in
      _packed_ s
    and _number_spaces_ s= 
      let _packed_ = pack (make_nt_parser _number_) (fun c ->c)in
      _packed_ s
    and _string_spaces_ s= 
      let _packed_ = pack (make_nt_parser _string_) (fun c ->c)in
      _packed_ s
    and _symbol_spaces_ s= 
      let _packed_ = pack (make_nt_parser _symbol_) (fun c ->c)in
      _packed_ s
      
       and _nil_spaces_ s= 
      let _packed_ = pack (make_nt_parser _nil_) (fun c ->c)in
      _packed_ s
      
    and _list_rounded_spaces_ s= 
      let _packed_ = pack (make_nt_parser _list_rounded_) (fun c ->c)in
      _packed_ s
    and _list_squered_spaces_ s= 
      let _packed_ = pack (make_nt_parser _list_squered_) (fun c ->c)in
      _packed_ s
    and _dotted_list_squered_spaces_ s= 
      let _packed_ = pack (make_nt_parser _dotted_list_squered_) (fun c ->c)in
      _packed_ s
    and _dotted_list_rounded_spaces_ s= 
      let _packed_ = pack (make_nt_parser _dotted_list_rounded_) (fun c ->c)in
      _packed_ s
    and _vector_rounded_spaces_ s= 
      let _packed_ = pack (make_nt_parser _vector_rounded_) (fun c ->c)in
      _packed_ s
    and _quoted_spaces_ s=   
      let _packed_ = pack (make_nt_parser _quoted_) (fun c ->c)in
      _packed_ s
    and _quasi_quoted_spaces_ s= 
      let _packed_ = pack (make_nt_parser _quasi_quoted_) (fun c ->c)in
      _packed_ s
    and _unquoted_spaces_ s=  
      let _packed_ = pack (make_nt_parser _unquoted_) (fun c ->c)in
      _packed_ s
    and _unquote_and_spliced_spaces_ s=   
      let _packed_ = pack (make_nt_parser _unquote_and_spliced_) (fun c ->c)in
      _packed_ s

        
and _diffed_ s= 
  let _packed_ = pack (diff _Sexpr_ _three_dots_spaces_) (fun a->a) in
  _packed_ s
(*
  and _nt_close_ s= 
  let _packed_ = pack (disj (char ']')  (char ')')) (fun a->a) in
  _packed_ s

  and _nt_open_ s= 
  let _packed_ = pack (disj (char '[')  (char '(')) (fun a->a) in
  _packed_ s

  and _nt_close_all_ s= 
  let _packed_ = pack (word "...") (fun a->a) in
  _packed_ s

  and _nt_dot_ s= 
  let _packed_ = pack (diff (char '.') (word "...")) (fun a->a) in
  _packed_ s

  and _nt_prefix_ s= 
  let _packed_ = pack (char '#') (fun a->a) in
  _packed_ s

  and _A_ s= 
  let _packed_ = pack (disj_list[_diffed_;_D_;_L_;_V_]) (fun a->a) in
  _packed_ s

  and _S_ s= 
  let _packed_ = pack (caten (disj_list[_D_;_L_;_V_]) _nt_close_all_) (fun (a,b)->a) in
  _packed_ s

  and _L_ s= 
  let _packed_ = pack (caten (caten _nt_open_ (star _A_)) (maybe _nt_close_)) (fun ((a,b),c)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) b Nil) in
  _packed_ s

  and _D_ s= 
  let _packed_ = pack (caten (caten (caten (caten _nt_open_ (plus _A_)) _nt_dot_) (diff _A_ _nt_close_all_)) (maybe _nt_close_)) (fun ((((a,b),c),d),e)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) b d) in
  _packed_ s

  and _V_ s= 
  let _packed_ = pack (caten (caten (caten _nt_prefix_ _nt_open_) (star _A_)) (maybe _nt_close_)) (fun (((a,b),c),d)->Vector(c)) in
  _packed_ s

  and _three_dots_spaces_ s=   
      let _packed_ = pack (make_nt_parser _S_) (fun c ->c)in
      _packed_ s;;
*)
and _disj_sexpr_helper_ s = 
  let _packed_ =pack (disj_list [_diffed_;_case_squered_dotted_list_spaces_;_case_rounded_dotted_list_spaces_;_case_rounded_list_;_case_squered_list_;_case_vector_]) (fun a->a) in
  _packed_ s

and _star_disj_sexpr_helper_ s=
  let _packed_ = pack (star _disj_sexpr_helper_) (fun a->a) in
  _packed_ s

  and _plus_disj_sexpr_helper_ s=
  let _packed_ = pack (plus _disj_sexpr_helper_) (fun a->a) in
  _packed_ s
  
and _case_rounded_list_ s= 
  let _packed_ = pack (caten (caten (char '(') _star_disj_sexpr_helper_) (maybe (char ')'))) (fun ((a,b),c)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) b Nil)in
  _packed_ s

  and _case_rounded_dotted_list_ s= 
  let _packed_ = pack (caten (caten (caten (caten (char '(') _plus_disj_sexpr_helper_)   (char '.') ) _disj_sexpr_helper_) (maybe (char ')'))) (fun ((((a,b),c),d),e)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) b d)in
  _packed_ s

  and _case_squered_list_ s= 
  let _packed_ = pack (caten (caten (char '[') _star_disj_sexpr_helper_) (maybe (char ']'))) (fun ((a,b),c)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) b Nil)in
  _packed_ s

 and _case_squered_dotted_list_ s= 
  let _packed_ = pack (caten (caten (caten (caten (char '[') _plus_disj_sexpr_helper_)  (char '.')) _disj_sexpr_helper_  ) (maybe (char ']'))) (fun ((((a,b),c),d),e)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) b d)in
  _packed_ s
  

      and _case_vector_ s= 
      let _packed_ = pack (caten (caten (caten (char '#')  (char '[') ) (star _disj_sexpr_helper_)) (maybe  (char ']') )) (fun (((a,b),c),d)->Vector(c)) in
      _packed_ s

  and _case_rounded_dotted_list_spaces_ s=   
      let _packed_ = pack (make_nt_parser _case_rounded_dotted_list_) (fun c ->c)in
      _packed_ s

      and _case_squered_dotted_list_spaces_ s=   
      let _packed_ = pack (make_nt_parser _case_squered_dotted_list_) (fun c ->c)in
      _packed_ s
      
    and _case_rounded_list_spaces_ s=   
      let _packed_ = pack (make_nt_parser _case_rounded_list_) (fun c ->c)in
      _packed_ s
      
    and _case_squered_list_spaces_ s=   
      let _packed_ = pack (make_nt_parser _case_squered_list_) (fun c ->c)in
      _packed_ s
      
    and _case_vector_spaces_ s=   
      let _packed_ = pack (make_nt_parser _case_vector_) (fun c ->c)in
      _packed_ s


and _three_dots_ s = 
  let _packed_ = pack (caten (disj_list [_case_squered_dotted_list_spaces_;_case_rounded_dotted_list_spaces_;_case_rounded_list_spaces_;_case_squered_list_spaces_;_case_vector_spaces_]) (word "...")) (fun (a,b)-> a) in
  _packed_ s 
  
and _three_dots_spaces_ s=   
      let _packed_ = pack (make_nt_parser _three_dots_) (fun c ->c)in
      _packed_ s;;

      

  
(* star sexpr parser*)
  let _star_sexpr_ = star _Sexpr_;;
  
let func ((s:sexpr),_) = s;;

let read_sexpr string =  (fun(a,b)->a )(_Sexpr_ (string_to_list string));;
let read_sexprs string = (fun(a,b)->a )((star _Sexpr_) (string_to_list string));;

end;; (* struct Reader *)

open Reader;;
