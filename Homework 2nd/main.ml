#use "policy.ml"

type ide = string
type expr =
 | CstI of int
 | CstB of bool
 | Var of ide
 | Let of ide * expr * expr
 | Prim of ide * expr * expr
 | If of expr * expr * expr
 | Fun of ide * expr 
 | LetRec of ide * expr * expr
 | Call of expr * expr
 | OpenSocket of ide * expr (** Abstracted operations on socket  *)
 | SendData of expr
 | ReadData 
 | CloseSocket
 | BuildPolicy of state list * state * transition list (** constructor to build a policy return corresponding value *)
 | DefPolicyIn of expr * expr (** constructor to set up a policy within evaluating of a expression  *)

type 'v env = (ide * 'v) list;;                           (**recurisive function *)
type envT = Int of int | Bool of bool | FunVal of envFun | RecFunVal of ide * envFun | Policy of policy
and envFun =  ide * expr * envT env 

(** BUILT IN POLICIES*)
(** @brief no write after read policy *)
let pNwAr = BuildPolicy(states,initialState,deltAdNwAr);;
(** @brief no a CloseSocket before an OpenSocket policy *)
let pNcBo = BuildPolicy(states,initialState,deltAdNcBo);;

(** routine operation for environment *)
let bind env (x : ide) (v : envT) = (x,v) :: env
let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x

(**
    @brief build a policy 
 *)
let buildPolicy (delta : transition list) (listOfs : state list ) (startS : state ) =
    let vaildPolicy = contains startS listOfs && isValid delta listOfs in
        begin
        match vaildPolicy with
        | true -> Policy({states = listOfs;sigma=policySigma;start=startS;transitions=delta})
        | false -> failwith("Wrong policy definition")
        end        
(**
    utility functions
 *)
let getValue (x : (envT * history)) = 
    begin
    match x with
    |(v,h) -> v
    end
let getHistory (x : (envT * history)) = 
    begin
    match x with
    |(v,h) -> h
    end

(** 
    @brief evaluate and check security policies over global execution history 

*)
let rec peval (e :expr) (r : envT env) (pStack : policyStack ) (h : history) : envT * history = match e with
    | CstI n -> (Int n, h) (** at this point all are obeyed so it can return computed value*)
    | CstB b -> (Bool b, h)
    | Var x -> (lookup r x,h)
    | Let(i,e1,e2) -> let tmp = peval e1 r pStack h in 
                                let v = getValue tmp in
                                    let h' = getHistory tmp in 
                                        let env1 = bind r i v in 
                                            peval e2 env1 pStack h'
    | Prim(ope, e1, e2) ->
     let tmp1 = peval e1 r pStack h in
     let v1 = getValue tmp1 in 
     let tmp2 = peval e2 r pStack (getHistory tmp1) in
     let v2 = getValue tmp2 in 
     begin
     match (ope, v1, v2) with
     | ("*", Int i1, Int i2) -> ((Int (i1 * i2)), getHistory tmp2)
     | ("+", Int i1, Int i2) -> ((Int (i1 + i2)), getHistory tmp2)
     | ("-", Int i1, Int i2) -> ((Int (i1 - i2)),getHistory tmp2)
     | ("=", Int i1, Int i2) -> ((Bool( i1 == i2)),getHistory tmp2)
     | ("<", Int i1, Int i2) -> ((Bool( i1 < i2)), getHistory tmp2)
     |  _ -> failwith "unknown primitive or wrong type"
     end
     | If(e1,e2,e3) -> let tmp = peval e1 r pStack h in
                                let guard = getValue tmp in
                                    let h' = getHistory tmp in 
                                    begin
                                    match guard with
                                    | Bool(true) -> peval e2 r pStack h'
                                    | Bool(false) -> peval e3 r pStack h'
                                    |_-> failwith("Guard must be boolean")
                                    end
    | Fun(param,body) -> (FunVal(param,body,r),h)
    | Call(fexp,param) -> let tmp = peval fexp r pStack h in 
                                let h' = getHistory tmp in
                                    let fclosure = getValue tmp  in
                                        begin
                                        match fclosure with
                                        | FunVal(x,body,envD) -> let tmp = peval param r pStack h' in
                                                                        let v = getValue tmp in 
                                                                            let env1 = bind envD x v in 
                                                                                    peval body env1 pStack (getHistory tmp)
                                        | RecFunVal(fname,(arg,body, envD)) -> let tmp = peval param r pStack h in
                                                                                    let v = getValue tmp in
                                                                                        let rEnv = bind envD fname fclosure in
                                                                                            let bEnv = bind rEnv arg v in
                                                                                                peval body bEnv pStack (getHistory tmp)
                                        | _ -> failwith("is not a function")
                                        end
    | LetRec(fname,funDef,lbody) -> begin
                                   match funDef with
                                   |Fun(i,fBody) -> let env1 = (bind r fname (RecFunVal(fname,(i,fBody,r)))) in
                                                            peval lbody env1 pStack h
                                   |_ -> failwith("is not a function definition")
                                   end
    | BuildPolicy(listOfs,startS,delta) -> (buildPolicy delta listOfs startS, h) (** builing policy *)
    | DefPolicyIn(pexp,e) -> let tmp = peval pexp r pStack h in (** getting policy *)
                                    let p = getValue tmp in
                                        let h' = getHistory tmp in 
                                            begin
                                            match p with
                                            | Policy(pval) -> let pStack1 = push pval pStack (** activating policy *)
                                                                in peval e r pStack1 h' 
                                            |_ -> failwith("First parameter is not a policy")
                                            end
    | OpenSocket(ip,eport) ->  let h1 = updateH openS h in (** adding operation to execution history *)
                                let allowed = checkPolicy pStack h1 in (** verifying of all active policies before executing operation *)
                                    begin
                                    match allowed with
                                    | true ->  let tmp = peval eport r pStack h1 in
                                                    let port = getValue tmp in 
                                                            begin
                                                            match port with
                                                            | Int(i) -> print_endline ("Socket opened ip " ^ ip ^ " port " ^ (string_of_int i));
                                                                        (Bool(true),getHistory tmp)
                                                            | _ -> (Bool(false),getHistory tmp)
                                                            end
                                    | false -> failwith("Policy framing broken")
                                    end
    | SendData(dexpr) -> let h1 = updateH sendD h in (** adding operation to execution history *)
                            let allowed = checkPolicy pStack h1 in (** verifying of all active policies before executing operation *)
                                begin
                                match allowed with
                                | true -> let tmp = peval dexpr r pStack h1 in 
                                                let data = getValue tmp in 
                                                    begin
                                                    match data with
                                                    | Int(i) ->     print_endline ("Data Sent " ^ (string_of_int i)) ;
                                                                    (Bool(true),h1)
                                                    | Bool(b) ->    print_endline ("Data Sent"  ^ (string_of_bool b)) ;
                                                                    (Bool(true),h1)
                                                    | _ -> failwith("wrong type value")
                                                    end
                                | false -> failwith("Policy framing broken")
                                end
    | ReadData -> let h1 = updateH readD h in (** adding operation to execution history *)
                    let allowed = checkPolicy pStack h1 in (** verifying of all active policies before executing operation *)
                    begin
                    match allowed with
                    | true ->  print_endline "Data read" ;
                              (Bool(true),h1)
                    | false -> failwith("Policy Framing broken")
                    end
    | CloseSocket ->  let h1 = updateH closeS h in (** adding operation to execution history *)
                        let allowed = checkPolicy pStack h1 in (** verifying of all active policies before executing operation *)
                        begin
                        match allowed with
                        | true ->   print_endline "Socket closed" ;
                                    (Bool(true),h1)
                        | false -> failwith("Policy Framing broken")
                        end


(**
 @brief evaluate e and enforce security policies by calling peval
 *)
let eval (e : expr) =
    let result = peval e [] [] epsilon in
        match result with
        |(v,_) -> v ;;

(** TEST *)
let testRegression = Call(Let("x", CstI 8 , Fun("y",Prim("-",Var "y", Var "x"))),CstI 10);;
(** case policy dNwAr broken  *)
let testNwArKo = DefPolicyIn(pNwAr, Let("x", ReadData, SendData(CstI 10)));;
(** case policy dNwAr obeyed *)
let testNwArOk = DefPolicyIn(pNwAr, Let("x", ReadData, ReadData));;
(** case policy dNcBo broken  *)
let testNcBoKo =  DefPolicyIn(pNcBo, Let("x", CloseSocket, OpenSocket("1.1.1.1", CstI(10))));;
(** case policy dNcBo obeyed *)
let testNcBoOk =  DefPolicyIn(pNcBo, Let("x", OpenSocket("127.0.0.1", CstI 8080),CloseSocket));;

(** case policies are being obeyed*)
let testNestedOk = DefPolicyIn(pNcBo, DefPolicyIn(pNwAr, Let("x", OpenSocket("1.1.1.1", CstI 80), SendData(CstI 10))));;
(**  case deeper policy is being broken*)
let testNestedKo = DefPolicyIn(pNcBo, DefPolicyIn(pNwAr, Let("x", ReadData, SendData(CstI 10))));;
(**  case top level policy is being broken*)
let testNestedKoTL = DefPolicyIn(pNcBo, DefPolicyIn(pNwAr, Let("x", ReadData, CloseSocket)));;

(** policy scope test 
    sequence write after read is being executed since is out of dNwAr scope
*)
let testScope = Let("x", DefPolicyIn(pNwAr, OpenSocket("201.23.34.0", CstI 8080)),Let("y",ReadData ,SendData(CstI 1234)));;

(** case policy is being defined as a variable *)
let testLet = Let("x",pNwAr, DefPolicyIn(Var "x", SendData(CstI 10)));;


(**
    example of a test execution 
    eval testScope;;
 *)




 (**recursive function test*)
(** 
let yequal0 = Prim("=",Var "y", CstI 0);;
let yminus1 = Prim("-", Var "y", CstI 1);;
let mul = Prim("*", Var "y", Call(Var "f", yminus1))
let fact = LetRec("f",
                        Fun("y",
                                Let("r",yequal0,If(Var "r", CstI 1, mul))
                            ),
                                Call(Var "f", CstI 5)
                    );;

eval fact;;
*)

