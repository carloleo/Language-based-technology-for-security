#use "dfa.ml"

(** POLICY DEFINITION *)
(** each relevant operation is being mapped into a symbol*)
let openS = 'o';;
let readD = 'r';;
let sendD = 'w';;
let closeS = 'c';;
let policySigma = openS :: readD :: sendD :: closeS :: [];; (** global alphabet provided *)
let epsilon = "";; (** empty history *)

(** @brief policy as dfa *)
type policy = dfa;;

(** @brief execution history as string*)
type history = string;;

(** @brief keep all active policies at some point of the program execution *)
type policyStack = policy list;;

(** @brief push policy p on policy stack pStack *)
let push (p : policy) (pStack : policyStack) = p :: pStack;;

(** @brief update execution history h adding operation op *)
let updateH (op : char) (h : history) = (String.make 1 op) ^ h;;

(**
    @brief check if execution history h is accept by active policies  
 *)
let rec checkPolicy (pStack : policyStack) (h : history) =
    begin
    match pStack with
    |[] -> true
    |x :: xs -> let satisfied = checkAccepts h x in
                    if(satisfied) then checkPolicy xs h
                    else false
    end
(**
    @brief check if all transitions has been defined on valid states and symbols
 *)
let rec isValid (delta : transition list) (listOfs : state list ) =
    begin
    match delta with
    | [] -> true
    | (s1,sy,s2) :: xs -> let result = contains sy policySigma && contains s1 listOfs && contains s2 listOfs in
                                begin
                                match result with
                                | true -> isValid xs listOfs
                                | false -> result
                                end
    end

(** DEFINITION OF BUILT IN POLICIES *)
let states = [Some(0);Some(1)];;
let initialState = Some(0);;

(** transition function for no write after read policy *)
let deltAdNwAr = [
        (Some(0), readD, Some(1));
        (Some(1), readD, Some(1));
        (Some(0), sendD, Some(0)); (** delta is not being defined for sendD into state 1 *)
        (Some(0), openS, Some(0));
        (Some(1), openS, Some(1));
        (Some(0), closeS, Some(0));
        (Some(1), closeS, Some(1))
        
    ];;
(** transition function for no a CloseSocket before an OpenSocket policy *)
let deltAdNcBo = [
        (Some(0), readD, Some(0));
        (Some(1), readD, Some(1));
        (Some(0), sendD, Some(0)); 
        (Some(1), sendD, Some(1));
        (Some(0), openS, Some(1));
        (Some(1), openS, Some(1)); (** delta is not being defined for closeS into state 0 *)
        (Some(1), closeS, Some(0)) (**after a CloseSocket comes back into state 0 *)
        
    ];;