type ide = string
type perm =  Read | Write | Create | Destroy  (** permissions *)
type expr =
 | CstI of int
 | CstB of bool
 | Var of ide
 | Let of ide * expr * expr
 | Prim of ide * expr * expr
 | If of expr * expr * expr
 | Fun of ide * expr * perm list (** lambda extended with permissions list*)
 | Call of expr * expr
 | OpenSocket of ide * expr (** Abstracted operations on socket  *)
 | SendData of expr
 | ReadData 
 | CloseSocket


(** polymorphic environment  *)
type 'v env = (ide * 'v) list;;
type envT = Int of int | Bool of bool | FunVal of envFun 
and envFun =  ide * expr * perm list * envT env (** closure extended with permissions list *)

(** data type used to keep track of 
    all permissions of active functions
*)
type permsStack = (perm list) list;;

(** routine operation for environment *)
let bind env (x : ide) (v : envT) = (x,v) :: env
let rec lookup env x =
   match env with
   | []        -> failwith (x ^ " not found")
   | (y, v)::r -> if x=y then v else lookup r x


(** MANAGEMENT OF PERMISSIONS  *)

(**
    @brief: push l on secEnv
 *)
let addPerms (secEnv : permsStack) (l : perm list) =  l :: secEnv

(**
    @brief: aux function for checkPerm
 *)
let rec auxCheck  (secEnv : permsStack) (p : perm) (r : bool) : bool  =
    match(secEnv)with
    | [] -> r
    | x :: xs -> let r' = List.mem p x in 
                            if(r') then auxCheck xs p r' (** keep inspecting stack *)
                            else false (** found active function such that does not have p *)

(**
    @brief: verify if all active functions have a permission
    @param: p permission to check
    @param: secEven 
    @param: r
 *)
let checkPerm (secEnv : permsStack) (p : perm) : bool = 
    auxCheck secEnv p false 

let rec eval (e : expr) (env : envT env) (secEnv : permsStack) : envT =
begin
    match e with
    | CstI(i) -> Int(i)
    | CstB(b) -> Bool(b)
    | Var(x)  -> lookup env x
    | Let(i,e1,e2) -> let v = eval e1 env secEnv in 
                            let env1 = bind env i v in 
                                eval e2 env1 secEnv 
    | Prim(ope, e1, e2) ->
     let v1 = eval e1 env secEnv in
     let v2 = eval e2 env secEnv in
     begin
     match (ope, v1, v2) with
     | ("*", Int i1, Int i2) -> (Int (i1 * i2))
     | ("+", Int i1, Int i2) -> (Int (i1 + i2))
     | ("-", Int i1, Int i2) -> (Int (i1 - i2))
     | ("=", Int i1, Int i2) -> (Bool( i1 == i2))
     | ("<", Int i1, Int i2) -> (Bool( i1 < i2))
     |  _ -> failwith "unknown primitive or wrong type"
     end
    | If(e1,e2,e3) -> let guard = eval e1 env secEnv in
                                begin
                                match guard with
                                | Bool(true) -> eval e2 env secEnv
                                | Bool(false) -> eval e3 env secEnv
                                |_-> failwith("Guard must be boolean")
                                end
    | Fun(param,body,perms) -> FunVal(param,body,perms,env)
    | Call(fexp,param) -> let f = eval fexp env secEnv in
                                    begin
                                    match f with
                                    | FunVal(x,body,perms,envD) -> let v = eval param env secEnv in
                                                                        let env1 = bind envD x v in  (** when a function is being called its permissions are being pushed on current permsStack *)
                                                                            let secEnv1 = addPerms secEnv perms in  
                                                                                eval body env1 secEnv1  (** evaluation of body using new permsStack instance *)
                                    | _ -> failwith("is not a function")
                                    end
    | OpenSocket(ide,eport) -> let guard = checkPerm secEnv Create in     (**Abstracted operations on socket *)
                                        begin 
                                        match guard with
                                        | true -> let port = eval eport env secEnv in
                                                            begin
                                                            match port with
                                                            | Int(i) -> print_endline ("Socket opend ip " ^ ide ^ " port " ^ (string_of_int i));
                                                                        Bool(true)
                                                            | _ -> Bool(false)
                                                            end
                                        | false -> failwith("Cannot execute OpenSocket")
                                        end
    | SendData(edata) -> let guard = checkPerm secEnv Write in
                            begin 
                            match guard with
                            | true -> let data = eval edata env secEnv in 
                                            begin
                                            match data with
                                            | Int(i) ->     print_endline ("Data Sent " ^ (string_of_int i)) ;
                                                            Bool(true)
                                            | Bool(b) ->    print_endline ("Data Sent"  ^ (string_of_bool b)) ;
                                                            Bool(true)
                                            | _ -> failwith("wrong type value")
                                            end
                            | false -> failwith("Cannot execute SendData")
                            end
    | ReadData -> let guard = checkPerm secEnv Read in 
                            begin
                            match guard with
                            | true -> print_endline "Data read" ;
                                      Bool(true)
                            | false -> failwith("Cannot execute ReadData")
                            end
    | CloseSocket -> let guard = checkPerm secEnv Destroy in
                            begin
                            match guard with
                            | true -> print_endline "Socket closed";
                                      Bool(true)
                            | false -> failwith("Cannot execute CloseSocket")
                            end
end

                                                    (************* TEST ************)

(** you can define security stack here *)

let secEnv = [] ;; (** no other active functions *)

let secEnv1 =  [[Write;Read];[Read;Create];[Read;Destroy]];; (** three active functions  
                                                            only Read permission is common to all
                                                            so just ReadData will be allowed*)

(** in secEnv all operations are allowed since they are being declared with right permissions *)
let testOpen = Let("f",
                    Fun("a", OpenSocket("1.1.1.1",CstI(8080)),[Create]),
                        Call(Var("f"),CstI(0))) ;; 
let testSend = Let("f",
                    Fun("a", SendData(CstI(2)),[Write]),
                        Call(Var("f"),CstI(2))) ;;
let testRead = Let("f",
                    Fun("a", ReadData,[Read]),
                        Call(Var("f"),CstI(2)));;
let testClose = Let("f",
                    Fun("a", CloseSocket,[Destroy]),
                        Call(Var("f"),CstI(2)));;

(** exemple
    eval testOpen [] secEnv
 *)

(** normal operations behaviour does not change  *)
let testRegression = Call(Let("x", CstI 8 , Fun("y",Prim("+",Var "y", Var "x"),[])),CstI 10);;
(** eval testRegression [] secEnv1
    - : envT = Int 18
*)

let nestedFunCallKo = Let("f",
                        Fun("a", SendData(CstI(2)),[Write]),
                             Let("g", 
                                Fun("b", Call(Var("f"),CstI(7)),[Read;Create;Write]), 
                                     Call(Var("g"),CstI(7))));;
(** eval nestedFunCallKo [] secEnv1
    will fail despite both f and g are being declared with Write permission
 *)

let nestedFunCallOk = Let("f",
                            Fun("a", ReadData,[Read]),
                                Let("g", Fun("b", Call(Var("f"),CstI(0)),[Create;Read]), 
                                    Call(Var("g"),CstI(0))));;
(** eval nestedFunCallOk [] secEnv 
    will succeed because both are being declared with Read permissions

    eval nestedFunCallOk [] secEnv1
    will succeed also in secEnv1

*)