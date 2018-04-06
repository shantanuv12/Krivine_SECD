(** The type of values *)
type boolean = true | false
type constant = INTEGER of int | BOOL of boolean
type identifier = string
type expression =
  | CONSTANT_EXPRESSION of constant
  | VAR of identifier
  | LAMBDA of (identifier * expression)
  | FUNCTION of (expression * expression)
  | CONDTIONAL of (expression * expression * expression)

type program = expression

type value =	(*did not implement a table cause a table basically is the bottom two matches, value and closure.*)
  | CONSTANT_VALUE of constant
  | CLOSURE of (env * identifier * expression)
  | NEW_CLOSURE of env* expression
and env = (identifier * value) list 
type stack = value list
type instruction =
  | EXPRESSION of expression
  | APPLY (*APPLY pops off two arguments from the stack and applies the second to the first*)
  | ADD (*add instruction between two integer values*)
type control = instruction list (*not an expression list? but rather an instruction list*)
(* The Dump register *)
type dump = (stack * env * control) list (*end of the world :P*)

(* The initial environment *)
let e_init = [("SHUBHAM",NEW_CLOSURE([],VAR("kandu"))) ; ("ankur" ,CONSTANT_VALUE(INTEGER(-1))); ("kandu" ,CONSTANT_VALUE(BOOL(false)))];;

(* Lookup function for environment to return value of a variable in the environment*)

let rec lookup id e =
  match e with
  | [] -> failwith "not found"
  | (id', v)::e' -> if id = id' then v else lookup id e' 

(** The transition function *)
(** transition: stack * env * control * dump -> value *)
let rec call_by_value = function
	|([v],e,[],[]) -> (*the program has finished and return the final values*) v
	| ([s1], e', [], (s, e, c)::d) -> call_by_value (s1::s, e, c, d)
	|(s , e , EXPRESSION ( CONSTANT_EXPRESSION ( some_constant ) ) ::c  ,  d   )  -> call_by_value (CONSTANT_VALUE(some_constant)::s,e,c,d)
	|(s , e , EXPRESSION ( LAMBDA ( my_identifier , my_expression ) ) ::c ,d )-> call_by_value ( CLOSURE(e,my_identifier,my_expression)::s , e , c ,d )
	|(s, e, (EXPRESSION (FUNCTION (t0, t1)))::c, d) -> call_by_value (s, e, (EXPRESSION t1)::(EXPRESSION t0)::APPLY::c, d)
	|(CONSTANT_VALUE(INTEGER(some_integer_val_1))::CONSTANT_VALUE(INTEGER(some_integer_val_2))::s , e , ADD::c ,d) -> call_by_value(CONSTANT_VALUE(INTEGER(some_integer_val_1+some_integer_val_2))::s , e , c ,d)
	|( ( CLOSURE (e', x, t))::v'::s, e, APPLY::c, d) -> call_by_value ([], (x, v')::e', [EXPRESSION t], (s, e, c)::d)
	|(s , e , EXPRESSION ( VAR ( some_variable ) ) ::c ,d ) ->call_by_value ((lookup some_variable e)::s , e ,c,d)
	| _ -> failwith "Stuck state"

let evaluate_secd t = call_by_value ([], e_init, [EXPRESSION t], [])

let rec call_by_name  = function 
	|(NEW_CLOSURE(env_1 , CONSTANT_EXPRESSION(some_constant)),s)-> CONSTANT_VALUE( some_constant )
	|(NEW_CLOSURE(env_1 , VAR(some_variable)),s )->(lookup some_variable env_1)
	|(NEW_CLOSURE(env_1 , LAMBDA( a_identifier , a_expression) ), NEW_CLOSURE(a,b)::s )->call_by_name( NEW_CLOSURE(((a_identifier,NEW_CLOSURE(a,b))::env_1) , a_expression) , s)
	|(NEW_CLOSURE(env_1 , FUNCTION(e1,e2)) ,s )-> call_by_name(NEW_CLOSURE(env_1 , e1) , NEW_CLOSURE(env_1 , e2)::s)
	| _ -> failwith "Stuck state"
;; 


let evaluate_krivine environ term = call_by_name (NEW_CLOSURE(environ ,term),[]) ;;

let e_1 = LAMBDA("SHUBHAM" , CONSTANT_EXPRESSION(INTEGER(2)));;
let e_2 = VAR("kandu");;
let e_3 = CONSTANT_EXPRESSION(INTEGER(9));;
let e_4 = FUNCTION(e_1,e_2);;
let v_1 = evaluate_krivine e_init e_2;;
let env_checker = [("SHUBHAM",CONSTANT_VALUE(INTEGER(15)));("ANKUR",NEW_CLOSURE(e_init , e_3))];;
let v_2 = evaluate_krivine env_checker e_3;;
let v_3 = evaluate_secd e_4;;
let instruct_1 = ADD;;
let my_stack = [];;
let my_environment = e_init;;
let my_control = [EXPRESSION(e_4); EXPRESSION(e_3);instruct_1];;
let my_dump = [];;
let run_this_secd = call_by_value(my_stack , my_environment , my_control , my_dump);; (**addition checker*)


