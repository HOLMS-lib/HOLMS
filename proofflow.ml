(* ========================================================================= *)
(* Structured proof-flow tactics for readable and robust HOL Light proofs.   *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

let FROM_TAC (lbls:string list) : tactic =
  fun asl,w ->
    let use_asm s =
      try find ((=) s o fst) asl
      with Failure _ -> failwith ("FROM_TAC: missing assumption: "^s) in
    let asl' = map use_asm lbls in
    ALL_TAC (asl',w);;

(* ------------------------------------------------------------------------- *)
(* Additional handy OCaml constants.                                         *)
(* ------------------------------------------------------------------------- *)

let true_tm = concl TRUTH;;
let false_tm = lhand (concl F_DEF);;

(* ------------------------------------------------------------------------- *)
(* Given a list l and a function f, filterpartition f l returns a pair of    *)
(* lists (yes,no), where no contains the elements of l on which f fails and  *)
(* yes is the result of successful applications of f.                        *)
(* It is equivalent to                                                       *)
(*   let yes,no = partition (can f) l in                                     *)
(*   map f yes,no                                                            *)
(* but avoids applying f twice to the elements where it succeedes.           *)
(* Comment: Used in TRY_ASSUM, however TRY_ASSUM has not been used so far.   *)
(* ------------------------------------------------------------------------- *)

let rec filterpartition f l =
  match l with
    [] -> [],l
  | h::t -> let yes,no = filterpartition f t in
            try f h::yes,no with Failure _ ->
            if yes = [] then [],l else yes,h::no;;

(* Test *)
(*
let f n = if n = 0 then 42 else fail() in
assert (filterpartition f [1; 0; 3] = ([42], [1; 3]));;
*)

(* ------------------------------------------------------------------------- *)
(* Handy rules and tactics.                                                  *)
(* ------------------------------------------------------------------------- *)

let DROP_TRUTH_ASSUM_TAC : tactic =
  fun (asl,w) as gl ->
    let asl' = filter (fun (_,th) -> concl th <> true_tm) asl in
    let gl' = if asl == asl' then gl else asl',w in
    ALL_TAC gl';;

(* Test *)
(*
g `1 + 1 = 2 /\ p ==> q`;;
e (INTRO_TAC "1 2");;
e (HYP_TAC "1" (CONV_RULE NUM_REDUCE_CONV));;
e DROP_TRUTH_ASSUM_TAC;;
check_fail e (UNDISCH_TAC `T`);;
*)

(* ------------------------------------------------------------------------- *)
(* TRIVIAL_ASSUM_TAC clear a goal by removing trivial assumptions: if        *)
(* falsum (`F`) occurs in the assumption list, it closes the goal.           *)
(* Otherwise, it eliminates all occurrence of verum (`T`) from the           *)
(* This might be useful as a final step of a tactic that perform some kind   *)
(* of simplyfication.                                                        *)
(* ------------------------------------------------------------------------- *)

let TRIVIAL_ASSUM_TAC : tactic =
  FIRST_ASSUM CONTR_TAC ORELSE DROP_TRUTH_ASSUM_TAC;;

(* Test *)
(*
g `(1 + 1 = 3 \/ 1 + 1 = 2) /\ p ==> q`;;
e (INTRO_TAC "(1 | 1) 2" THEN HYP_TAC "1" (CONV_RULE NUM_REDUCE_CONV));;
e TRIVIAL_ASSUM_TAC;;
e TRIVIAL_ASSUM_TAC;;
check_fail e (UNDISCH_TAC `T`);;
*)

(* ------------------------------------------------------------------------- *)
(* (TRY_ASSUM ttac) is a tactic that filters the assumptions of a goal by    *)
(* applying the thm_tactic ttac. It removes the assumptions on which ttac    *)
(* succeeds and applyes all the resulting tactics to the goal.               *)
(* It is roughly equivalent to                                               *)
(*   REPEAT (FIRST_X_ASSUM ttac)                                             *)
(* with the following three key differences:                                 *)
(*   - it applies ttac exactly once to each assumption in the goal;          *)
(*   - it fails if any of the resulting tactics fails;                       *)
(*   - apply the resulting tactics after the filtering of the assumption.    *)
(* !!! WRONG Example !!!:                                                    *)
(*   TRY_ASSUM SUBST_VAR_TAC                                                 *)
(* ------------------------------------------------------------------------- *)

let TRY_ASSUM : thm_tactic -> tactic =
  fun ttac (asl,w) ->
    let tacl,asl' = filterpartition (ttac o snd) asl in
    EVERY tacl (asl',w);;

(* Test *)
(*
g `1 = x /\ p /\ y = 2 ==> x + y = 3`;;
e STRIP_TAC;;
e (TRY_ASSUM SUBST_VAR_TAC);;
check_fail e (UNDISCH_TAC `2 = y`);;
e NUM_REDUCE_TAC;;
top_thm();;
*)

(* Test *)
(*
g `y + y = x /\ p /\ y = 1 ==> x + y = 3`;;
e STRIP_TAC;;
e (TRY_ASSUM SUBST_VAR_TAC);;
check_fail e (UNDISCH_TAC `2 = y`);;
e NUM_REDUCE_TAC;;
top_thm();;
*)



(* ------------------------------------------------------------------------- *)
(* Da cancellare(?)                                                          *)
(* ------------------------------------------------------------------------- *)

let TRUTH_ASSUME_TAC : thm_tactic =
  fun th -> if concl th = true_tm then ALL_TAC else
            failwith "TRUTH_ASSUME_TAC";;

let DISCARD_DUPLICATED_ASSUM_TAC : thm_tactic =
  fun th (asl,w as g) ->
    if exists (fun a -> aconv (concl th) (concl(snd a))) asl then ALL_TAC g
    else failwith "DISCARD_DUPLICATED_ASSUM_TAC";;

let DISCARD_TAC : thm_tactic =
  fun th -> TRUTH_ASSUME_TAC th ORELSE DISCARD_DUPLICATED_ASSUM_TAC th;;

(* ------------------------------------------------------------------------- *)
(* Forse utile nei test per introdurre facilmente i potesi duplicate         *)
(*  oppure `F` e `T` che invece STRIP_TAC elimina automaticamente.           *)
(* ------------------------------------------------------------------------- *)

let BASIC_STRIP_ASSUME_THEN : thm_tactical =
  REPEAT_TCL (CONJUNCTS_THEN ORELSE_TCL DISJ_CASES_THEN);;

let BASIC_STRIP_ASSUME_TAC : thm_tactic =
  BASIC_STRIP_ASSUME_THEN ASSUME_TAC;;

let EQTF_INTRO th = try EQF_INTRO th with Failure _ -> EQT_INTRO th;;

let CLEAR_CONV th : conv = REWRITE_CONV[EQTF_INTRO th];;

(* Test *)
(* CLEAR_CONV (ARITH_RULE `1 + 1 = 2`) `q /\ 1 + 1 = 2 \/ p`;; *)

let CLEAR_RULE th = CONV_RULE (CLEAR_CONV th);;

(* Clear the conclusion of a goal by rewriting a literal. *)
let CLEAR_TAC : thm_tactic =
  fun th ->
    FIRST [MATCH_ACCEPT_TAC th;
           CHANGED_TAC (CONV_TAC (CLEAR_CONV th));
           FAIL_TAC ("CLEAR_TAC: "^string_of_term(concl th))];;

let ASM_CLEAR_TAC : tactic =
  ASSUM_LIST (MAP_EVERY (TRY o CLEAR_TAC));;

let SHOW_TAC tm : tactic =
  SUBGOAL_THEN tm CLEAR_TAC;;

(* Clear both assumptions and conclusion of a goal. *)
let CLEAR_GOAL_TAC : thm_tactic =
  fun th ->
    let conv = CLEAR_CONV th in
    let rule = CONV_RULE conv in
    let tac = RULE_ASSUM_TAC rule THEN
              TRY (FIRST_ASSUM CONTR_TAC) THEN
              CONV_TAC conv THEN
              DROP_TRUTH_ASSUM_TAC in
    CHANGED_TAC tac ORELSE
    FAIL_TAC ("CLEAR_GOAL_TAC: "^string_of_term(concl th));;

let THEN1 (tac1:tactic) (tac2:tactic) : tactic =
  tac1 THENL [BY tac2; ALL_TAC];;

let THEN0 (tac1:tactic) (tac2:tactic) : tactic =
  tac1 THENL [tac2; ALL_TAC];;

let CLEAR_ASSUM_TAC : thm_tactic =
  fun th -> CLEAR_GOAL_TAC th THEN ASSUME_TAC th;;

let CLEAR_LABEL_TAC s : thm_tactic =
  fun th -> CLEAR_GOAL_TAC th THEN LABEL_TAC s th;;

let LABEL_SHOW_TAC s tm : tactic =
  SUBGOAL_THEN tm (CLEAR_LABEL_TAC s);;

let CASES_THEN ttac tm =
  DISJ_CASES_THEN ttac (SPEC tm EXCLUDED_MIDDLE);;

let LABEL_CASES_TAC s = CASES_THEN (LABEL_TAC s);;
let ASM_CASES_TAC = LABEL_CASES_TAC "";;
let CLEAR_CASES_TAC tm = CASES_THEN CLEAR_ASSUM_TAC tm;;

g `(p \/ q) /\ (if p then a else b) ==> q /\ p`;;
e STRIP_TAC;;
e (CLEAR_CASES_TAC `p:bool`);;

g `p /\ q ==> q \/ p`;;
e (CLEAR_CASES_TAC `p:bool`);;
top_thm();;
