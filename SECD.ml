exception Unmatch;;
exception EmptyStack;;
open List;;
type var=string;;
type exp =| If_then_else of exp* exp * exp
          | Const of int
          | Bool of bool
          | Abs of exp
          | Var of var
          | Succ of exp
          | Pred of exp
          | Plus of exp * exp
          | Subtract of exp * exp
          | Mult of exp * exp
          | Div of exp * exp
          | Mod of exp * exp
          | Exp of exp * exp
          | Not of exp
          | And of exp * exp
          | Or of exp * exp
          | Imp of exp * exp
          | Equals of exp * exp
          | Grthan of exp * exp
          | Lesthan of exp * exp
          | Grteql of exp * exp
          | Leseql of exp * exp
          | Tup of exp list
          | Proj of exp * exp
          | Lambda of (exp * exp)
          | Compose of exp * exp;;

type opcode =CONST of int
            | BOOL of bool
            | LOOKUP of var
            | ABS
            | PLUS
            | MINUS
            | MULT
            | DIV
            | MOD
            | SUCC
            | PRED
            | EXP
            | NOT
            | AND
            | OR
            | IMP
            | EQUALS
            | GRTHAN
            | LESTHAN
            | GRTEQL
            | LESEQL
            | TUP of opcode list list
            | PROJ
            | RET
            | CLOS of (exp * (opcode list))
            | APP;;

type value=Integer of int| Boolean of bool | Tuple of value list| Clos of (table * var * (opcode list))
and table = (var * value) list;;

type stack = value list;;

type dump= (stack * table * opcode list) list;;

let add (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1+n2)
|(_,_)-> raise Unmatch;;
let sub (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1-n2)
|(_,_)-> raise Unmatch;;
let mult (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1*n2)
|(_,_)-> raise Unmatch;;
let div (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1/n2)
|(_,_)-> raise Unmatch;;
let modulus (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1 mod n2)
|(_,_)-> raise Unmatch;;
let exp (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (int_of_float(float_of_int(n1) ** float_of_int(n2)))
|(_,_)->raise Unmatch;;
let succ e1=match e1 with
Integer e1->Integer (e1+1)
|_-> raise Unmatch;;
let pred e1=match e1 with
Integer n1->Integer (n1+1)
|_-> raise Unmatch;;
let abs e1=match e1 with
Integer n1-> if n1>0 then Integer n1 else Integer (-n1)
|_->raise Unmatch;;
let andl (e1,e2) =match (e1,e2) with
(Boolean b1,Boolean b2)-> Boolean (b1 && b2)
|(_,_)->raise Unmatch;;
let orl (e1,e2) =match (e1,e2) with
(Boolean b1,Boolean b2)-> Boolean (b1 || b2)
|(_,_)->raise Unmatch;;
let notl e1=match e1 with
Boolean b->Boolean (not b)
|_->raise Unmatch;;
let implies (e1,e2)=match (e1,e2) with
(Boolean false,Boolean false)->Boolean true
|(Boolean false,Boolean true)->Boolean true
|(Boolean true,Boolean false)->Boolean false
|(Boolean true,Boolean true)->Boolean true
|(_,_)->raise Unmatch;;
let equals (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1=n2)
|(_,_)->raise Unmatch;;
let greater (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1>n2)
|(_,_)->raise Unmatch;;
let greateq (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1>=n2)
|(_,_)->raise Unmatch;;
let lesser (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1<n2)
|(_,_)->raise Unmatch;;
let lesseql (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1<=n2)
|(_,_)->raise Unmatch;;


let extract_int a=match a with
Integer n->n
| _->raise Unmatch;;


let rho_fun=function
"x"->Integer 3
| "y"-> Integer 4
| _ -> Integer 0;;

let rho_lis=[("x",Integer 3);("y",Integer 4);("z",Boolean true)];;

let rec lookup (env:table) (variable:string)= match env with
    []-> failwith "Not found"
|   ((var1,val1)::env')-> if variable=var1 then val1 else lookup env' variable;;

let rec eval rho e=match e with
Const n->Integer n
| Bool b-> Boolean b
| Var x-> lookup rho x
| Abs n-> abs (eval rho n)
| Succ n-> succ (eval rho n)
| Pred n-> pred (eval rho n)
| Plus (n1,n2)-> add (eval rho n1,eval rho n2)
| Subtract (n1,n2)-> sub (eval rho n1,eval rho n2)
| Mult (n1,n2)-> mult (eval rho n1,eval rho n2)
| Div (n1,n2)-> div (eval rho n1,eval rho n2)
| Mod (n1,n2)-> modulus (eval rho n1,eval rho n2)
| Exp (n1,n2)-> exp (eval rho n1,eval rho n2)
| Not n-> notl (eval rho n)
| And (n1,n2)-> andl (eval rho n1,eval rho n2)
| Or (n1,n2)-> orl (eval rho n1,eval rho n2)
| Imp (n1,n2)-> implies (eval rho n1,eval rho n2)
| Equals (n1,n2)-> equals (eval rho n1,eval rho n2)
| Grthan (n1,n2)-> greater (eval rho n1,eval rho n2)
| Grteql (n1,n2)-> greateq (eval rho n1,eval rho n2)
| Lesthan (n1,n2)-> lesser (eval rho n1,eval rho n2)
| Leseql (n1,n2)-> lesseql (eval rho n1,eval rho n2)
| Proj (n1,Tup n2)-> eval rho (List.nth n2 (extract_int (eval rho n1)))
|_-> raise Unmatch;;

let rec compile e=match e with
Const n->[CONST n]
| Var x->[LOOKUP x]
| Bool b->[BOOL b]
| Tup t->[(TUP (List.map compile t))]
| Abs n->(compile n)@[ABS]
| Succ n->(compile n)@[SUCC]
| Pred n->(compile n)@[PRED]
| Plus (n1,n2)->(compile n1)@(compile n2)@[PLUS]
| Subtract (n1,n2)->(compile n1)@(compile n2)@[MINUS]
| Mult (n1,n2)->(compile n1)@(compile n2)@[MULT]
| Div (n1,n2)->(compile n1)@(compile n2)@[DIV]
| Mod (n1,n2)->(compile n1)@(compile n2)@[MOD]
| Exp (n1,n2)->(compile n1)@(compile n2)@[EXP]
| Not n->(compile n)@[NOT]
| And (n1,n2)->(compile n1)@(compile n2)@[AND]
| Or (n1,n2)->(compile n1)@(compile n2)@[OR]
| Imp (n1,n2)->(compile n1)@(compile n2)@[IMP]
| Equals (n1,n2)->(compile n1)@(compile n2)@[EQUALS]
| Grthan (n1,n2)->(compile n1)@(compile n2)@[GRTHAN]
| Grteql (n1,n2)->(compile n1)@(compile n2)@[GRTEQL]
| Lesthan (n1,n2)->(compile n1)@(compile n2)@[LESTHAN]
| Leseql (n1,n2)->(compile n1)@(compile n2)@[LESEQL]
| Proj (n1,n2)->(compile n1)@(compile n2)@[PROJ]
| Lambda(var,exp)->[CLOS(var,compile exp)]
| Compose(e1,e2)->compile(e1)@compile(e2)@[APP];;

let rec map f lis e d =match lis with
[]->[]
|x::xs -> (f ([],e,x,d))::(map f xs e d);;

let rec execute (s,e,c,d)=match (s,e,c,d) with
  (s',e',[],d')->hd s'
| (s,e',(CONST n)::c',d')->execute ((Integer n)::s,e',c',d')
| (s,e',(LOOKUP x)::c',d')->execute ((lookup e' x)::s,e',c',d')
| (s,e',(BOOL b)::c',d')->execute ((Boolean b)::s,e',c',d')
(*| (s,e',(TUP t)::c',d')->execute ((Tuple (map execute t e' d'))::s,e',c',d')*)
| ((Integer n)::s,e',ABS::c',d')->execute (abs (Integer n)::s,e',c',d')
| ((Integer n)::s,e',SUCC::c',d')->execute (succ (Integer n)::s,e',c',d')
| ((Integer n)::s,e',PRED::c',d')->execute (pred (Integer n)::s,e',c',d')
| ((Integer n2)::(Integer n1)::s',e',PLUS::c',d')->execute (add (Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',MINUS::c',d')->execute (sub (Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',MULT::c',d')->execute (mult (Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',DIV::c',d')->execute (div (Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',MOD::c',d')->execute (modulus (Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',EXP::c',d')->execute (exp (Integer n1,Integer n2)::s',e',c',d')
| ((Boolean b)::s',e',NOT::c',d')->execute ((notl (Boolean b))::s',e',c',d')
| ((Boolean b2)::(Boolean b1)::s',e',AND::c',d')->execute (andl (Boolean b1,Boolean b2)::s',e',c',d')
| ((Boolean b2)::(Boolean b1)::s',e',OR::c',d')->execute (orl (Boolean b1,Boolean b2)::s',e',c',d')
| ((Boolean b2)::(Boolean b1)::s',e',IMP::c',d')->execute (implies (Boolean b1,Boolean b2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',EQUALS::c',d')->execute (equals (Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',GRTHAN::c',d')->execute (greater(Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',GRTEQL::c',d')->execute (greateq(Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',LESTHAN::c',d')->execute (lesser(Integer n1,Integer n2)::s',e',c',d')
| ((Integer n2)::(Integer n1)::s',e',LESEQL::c',d')->execute (lesseql(Integer n1,Integer n2)::s',e',c',d')
(*| ((Tuple t)::(Integer n1)::s',e',PROJ::c',d')->execute((List.nth t (extract_int (Integer n1)))::s',e',c',d') *)
| (s',e',CLOS(Var v,c)::c1,d')-> execute(Clos(e',v,c)::s',e',c1,d')
| ((Integer n1)::Clos(e1,v1,c1)::s',e',APP::c',d')-> execute([],(v1,Integer n1)::e1,c1,(s',e',c')::d')
| ((Boolean b)::Clos(e1,v1,c1)::s',e',APP::c',d')-> execute([],(v1,Boolean b)::e1,c1,(s',e',c')::d')
| ((Integer n1)::s',e',RET::c',(s1,e1,c1)::d')-> execute((Integer n1)::s1,e1,c1,d')
| ((Boolean b)::s',e',RET::c',(s1,e1,c1)::d')-> execute((Boolean b)::s1,e1,c1,d')
| _->raise EmptyStack;;
