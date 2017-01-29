(*
 * Put the code for your interpreter in this file. Your interpreter should
 * be based on the big-step (natural-style) operational semantics for IMP
 * that we went over in class (and in Winskel's book). 
 *
 * This skeleton file includes one implementation of states (based on
 * OCaml's Map) and evaluations for AExps. 
 *)

open Imp (* imp.ml has the definitions for our IMP datatypes *) 

(* Our operational semantics has a notion of 'state' (sigma). The type
 * 'state' is a map (LocMap.t) from 'loc' to 'int'.
 * 
 * See http://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.S.html
 * 
 * The helper functions below wrap the library below so that you need
 * not use the library functions directly.
 *)

module LocMap = Map.Make(struct
			   type t = loc
			   let compare = compare
			 end)
type state = int LocMap.t

(* The empty state. *)
let empty_state: state = LocMap.empty

(* Given a state sigma, return the current value associated with variable 'x'. 
 * For our purposes all uninitialized variables start at 0. 
 *)

let lookup (sigma: state) (x: loc) : int = 
  try
    LocMap.find x sigma
  with Not_found -> 0 

(* Given a state sigma, return a new state like sigma except that variable x
 * maps to integer n. 
 *)
let update (sigma: state) (x: loc) (n: int) : state = LocMap.add x n sigma

(* Evaluates an aexp given the state 'sigma'. *) 
let rec eval_aexp (a: aexp) (sigma: state) : int = match a with
  | Const n -> n
  | Var(loc) -> lookup sigma loc
  | Add(a1,a2) -> eval_aexp a1 sigma + eval_aexp a2 sigma 
  | Sub(a1,a2) -> eval_aexp a1 sigma - eval_aexp a2 sigma 
  | Mul(a1,a2) -> eval_aexp a1 sigma * eval_aexp a2 sigma 

(* 
  | Div(a1,a2) -> 
  | Mod(a1,a2) -> 
*)

(* Evaluates a bexp given the state 'sigma'. *) 
let rec eval_bexp (b: bexp) (sigma: state) : bool = match b with
  | True -> true
  | False -> false 
(*
 * fill in the missing cases and code
  | EQ(a1,a2) -> 
  | LE(a1,a2) ->
  | Not b -> 
  | And(b1,b2) -> 
  | Or(b1,b2) -> 
 *) 
  | _ -> 
    (* you must put real code here *) 
    failwith "Warning! BExp not yet implemented!"

(* Evaluates a com given the state 'sigma'. *) 
let rec eval_com (c: com) (sigma:state) : state = match c with
  | Skip -> sigma
  | Print (a:aexp) ->
       let value = eval_aexp a sigma in begin
             Printf.printf "%d" value; 
             sigma
       end
(*
 * fill in the missing cases and code 
  | Set(id,a) -> 
  | Seq(c1,c2) -> 
  | If(b,c1,c2) -> 
  | While(b,c) -> 
  | Let(id,a,c) -> 
 *) 
  | _ -> 
    (* you must put real code here *)
    failwith "Warning! Com not yet implemented!"
