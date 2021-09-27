(**
    DFA definition
 *)

type state = int  option;;
type symbol = char;;
type transition = state * symbol * state;;

type dfa = 
{
    states : state list;
    sigma : symbol list;
    start : state;
    transitions : transition list;
    (*accepting : state list;* all states are accepted) *)
}

let states (dfa : dfa) = dfa.states;;

(** utility functions *)
let valueOfState (s : state) = 
    match s with
    |Some i -> i
    |_ -> failwith "Exception wrong state";;

let explode s =
    let rec expl i l = 
        if(i < 0) then l
        else expl (i-1) (s.[i] :: l )
        in expl (String.length s - 1 ) [];;

let contains e l = List.mem e l;;

(** UNIT TEST
let sl =  explode "HelloMom";;
contains 'o' sl;; *)

(**
    @brief verify if dfa recognizes the string str
 *)
let checkAccepts str dfa =
    let symbols = explode str in
        let transition state symbol =
            let rec find_state l =
                begin
                match l with
                |(Some(s1),sym,Some(s2)) :: tl -> begin
                                                  match state with
                                                  |Some(s_curr) ->
                                                            if(s_curr == s1 && symbol == sym) then Some(s2)
                                                            else find_state tl
                                                  |_-> None;
                                                  end
                |_-> None
                end
            in find_state dfa.transitions
        in
            let final_state = 
                let rec h symbol_list = 
                    begin
                    match symbol_list with
                    |[hd] -> (transition dfa.start hd)
                    |hd :: tl -> (transition (h tl) hd)
                    |_ -> failwith "empty list of symbols"
                    end
                in  h symbols
            in
                match final_state with
                | Some(i) -> true
                |_-> false;;


(** 
    UNIT TEST
let d : dfa  = 
{
    states = [Some(0);Some(1)];
    sigma = ['r';'w'];
    start = Some(0);
    transitions =
        [
            (Some(0),'r',Some(0));
            (Some(1),'r',Some(1));
            (Some(0),'w',Some(0));
            
            
        ]
} 
in checkAccepts "wr" d;;
*)
