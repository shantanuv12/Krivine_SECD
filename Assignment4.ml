type var = string;;
type boolean=true|false;;
type const = Integer of int| Bool of bool;;
type exp = Var of var
           |Constant of const
           |Lambda of (var * exp)
           |Compose of (exp * exp);;
type value = Const of const| Closure of (table * exp)
and table = (var * value) list;;
type stack = value list;;
let rec lookup (env:table) (variable:var)= match env with
    []-> failwith "Not found"
|   ((var1,val1)::env')-> if variable=var1 then val1 else lookup env' variable;;

let rec call_by_name= function
    |(Closure(envm, Constant(Integer n)),s)-> Const (Integer n)
    |(Closure(envm, Constant(Bool n)),s)-> Const (Bool n)
    |(Closure(envm, Var v),s)-> lookup envm v
    |(Closure(envm, Lambda(var,exp)),Closure(a,b)::s)->( match b with
                                                        |Constant n->call_by_name (Closure((var,Const n)::envm,exp),s)
                                                        |Var v -> call_by_name (Closure((var,lookup a v)::envm,exp),s)
                                                        | _-> failwith "Wromg implementation")
    |(Closure(envm, Compose(exp1, exp2)),s)-> call_by_name (Closure(envm,exp1),Closure(envm,exp2)::s)
    | _-> failwith "Cannot be evaluated";;

let krivine_eval env expr= call_by_name (Closure(env,expr),[]);;
