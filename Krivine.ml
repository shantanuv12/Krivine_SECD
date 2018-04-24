type var=string;;
type exp= NIL
          | Var of var
          | Integer of int
          | Boolean of bool
          | If_then_Else of exp * exp * exp
          | BIND of var * exp
          | Compose of exp * exp
          | Lambda of var * exp
          | Plus of exp * exp
          | Subtract of exp * exp
          | Mult of exp * exp
          | And of exp * exp
          | Or of exp * exp
          | Equals of exp * exp
          | Grthan of exp * exp
          | Lesthan of exp * exp
          | Grteql of exp * exp
          | Leseql of exp * exp;;


type closure= Closure of (env * exp )
and env=(var * closure) list;;

type clstack= closure list;;
exception Unmatch;;


let rec find_var var env= match env with
[]->failwith "variable not declared"
| (v,cl)::tl -> if (v=var) then (match cl with
                                Closure(env,Lambda (x,y)) -> Closure((v,cl)::env,Lambda (x,y))
                                | _-> cl
                                ) else find_var var tl
;;
let add (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))->Closure([],Integer (n1+n2))
|(_,_)-> raise Unmatch;;
let sub (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))->Closure([],Integer (n1-n2))
|(_,_)-> raise Unmatch;;
let mult (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))->Closure([],Integer (n1*n2))
|(_,_)-> raise Unmatch;;
let andl (e1,e2) =match (e1,e2) with
|(Closure(env1,Boolean b1), Closure(env2,Boolean b2))-> Closure([],Boolean (b1 && b2))
|(_,_)->raise Unmatch;;
let orl (e1,e2) =match (e1,e2) with
|(Closure(env1,Boolean b1), Closure(env2,Boolean b2))-> Closure([],Boolean (b1 || b2))
|(_,_)->raise Unmatch;;
let equals (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))-> Closure([],Boolean (n1=n2))
|(Closure(env1,Boolean b1), Closure(env2,Boolean b2))-> Closure([],Boolean (b1=b2))
|(_,_)->raise Unmatch;;
let greater (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))->Closure([],Boolean (n1>n2))
|(_,_)->raise Unmatch;;
let greateq (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))->Closure([],Boolean (n1>=n2))
|(_,_)->raise Unmatch;;
let lesser (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))->Closure([],Boolean (n1<n2))
|(_,_)->raise Unmatch;;
let lesseql (e1,e2)=match (e1,e2) with
|(Closure(env1,Integer n1), Closure(env2,Integer n2))->Closure([],Boolean (n1<=n2))
|(_,_)->raise Unmatch;;


let if_then_else cl e1 e2 env=match cl with
| Closure(_,Boolean b)-> if b then Closure(env,e1) else Closure(env,e2)
|_-> failwith "Invalid Operation";;

let exec_fun cl stack=match (cl,stack) with
| (_,[])-> failwith "Invalid Function call"
| (Closure(env,Lambda(v,e)),hd::tl)-> (Closure((v,hd)::env,e),tl)
| _-> failwith "Invalid Call";;

let rec call_by_name (a,b)=match (a,b) with
    |(Closure(envm,NIL),s)-> Closure(envm,NIL)
    |(Closure(envm, Var v),s)-> let cl_new= (find_var v envm) in call_by_name (cl_new,s)
    |(Closure(envm, Integer n),s)-> Closure(envm, Integer n)
    |(Closure(envm, Boolean b),s)-> Closure(envm, Boolean b)
    |(Closure(envm, Plus(e1,e2)),s)-> call_by_name (add(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Subtract(e1,e2)),s)-> call_by_name (sub(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Mult(e1,e2)),s)-> call_by_name (mult(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, And(e1,e2)),s)-> call_by_name (andl(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Or(e1,e2)),s)-> call_by_name (orl(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Equals(e1,e2)),s)-> call_by_name (equals(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Grthan(e1,e2)),s)-> call_by_name (greater(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Grteql(e1,e2)),s)-> call_by_name (greateq(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Lesthan(e1,e2)),s)-> call_by_name (lesser(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Leseql(e1,e2)),s)-> call_by_name (lesseql(call_by_name (Closure(envm,e1),[]),call_by_name (Closure(envm,e2),[])),s)
    |(Closure(envm, Lambda(var,exp)),Closure(env,ex)::s)-> let (cl,st)=exec_fun a b in (call_by_name (cl,st))
    |(Closure(envm, Compose(exp1, exp2)),s)-> (call_by_name (Closure(envm,exp1),Closure(envm,exp2)::s))
    |(Closure(envm, If_then_Else(e1,e2,e3)),s)-> let res1=call_by_name (Closure(envm,e1),[]) in call_by_name (if_then_else res1 e2 e3 envm,s)
    |(Closure(envm, BIND(v,e)),s)-> call_by_name (Closure((v,Closure(envm,e))::envm,NIL),s)
    | _-> failwith "Cannot be evaluated";;

let krivine_eval env expr= call_by_name (Closure(env,expr),[]);;
