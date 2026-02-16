(* ========================================================================= *)
(* Decision procedure for the modal logic B.                                 *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let IN_RSF_CLAUSES = prove
 (`!W:W->bool R.
     (W,R) IN RSF
     ==> (!x. x IN W ==> R x x) /\
         (!x y. R x y ==> R y x) /\
         (!w w'. R w w'
                 ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
         (!w p. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w')`,
  REWRITE_TAC[IN_RSF; IN_FINITE_FRAME; REFLEXIVE; SYMMETRIC] THEN
  MESON_TAC[HOLDS_LEFT_BOX]);;

let B_COMPLETENESS_NUM =
 let B_COMPLETENESS_THEOREM_NUM =
   REWRITE_RULE[num_INFINITE]
     (INST_TYPE [`:num`,`:A`] B_COMPLETENESS_THM_GEN) in
 prove
 (`!p. (!W:num->bool R.
          (W,R) IN RSF
          ==> !V w. w IN W /\ R w w ==> holds (W,R) V p w)
       ==> [B_AX . {} |~ p]`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC B_COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN
  INTRO_TAC "![W] [R]; rf" THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[IN_RSF_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let IN_RSF_RULES =
  let tm = `(W:num->bool,R) IN RSF` in
  let th = MATCH_MP IN_RSF_CLAUSES (ASSUME tm) in
  CONJUNCTS th;;

let B_TAC : tactic =
  GEN_HOLMS_TAC MATCH_BOX_RIGHT_TAC B_COMPLETENESS_NUM IN_RSF_RULES;;

holms_register_tactic `B_AX` B_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*
let PREPARE_TAC = HOLMS_PREPARE_TAC B_COMPLETENESS_NUM;;
let SATURATE_TAC = HOLMS_SATURATE_TAC IN_RSF_RULES;;
let STEP_TAC = HOLMS_STEP_TAC SATURATE_TAC;;
let INNER_TAC = INNER_HOLMS_TAC SATURATE_TAC;;
let box_right_tac = BOX_RIGHT_THEN SATURATE_TAC;;
let right_tac = HOLMS_RIGHB_TAC SATURATE_TAC;;
*)

g `[B_AX . {} |~ Box (Atom a && Atom b) <->
                 Box Atom a && Box Atom b]`;;
e B_TAC;;
top_thm();;

(* ------------------------------------------------------------------------- *)
(* Countermodels.                                                            *)
(* ------------------------------------------------------------------------- *)

let B_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `RSF:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

(* ------------------------------------------------------------------------- *)
(* Experiments.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Axioms *)
HOLMS_RULE `!a. [B_AX . {} |~ a --> Box Diam a]`;;
HOLMS_RULE `!a. [B_AX . {} |~ Box a --> a]`;;

(* ------------------------------------------------------------------------- *)
(* Non-axiom examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* T_AX *)
HOLMS_RULE `!a. [B_AX . {} |~ Box a --> a]`;;

(* K4_AX *)
let tm = `!a. [B_AX . {} |~ Box a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
B_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* S5_AX *)
let tm = `!a. [B_AX . {} |~ Diam a --> Box Diam  a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
B_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* GL_AX *)
let tm = `!a. [B_AX . {} |~ Box (Box a --> a) --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
B_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* ------------------------------------------------------------------------- *)
(* Further examples.                                                         *)
(* ------------------------------------------------------------------------- *)

let tm = `!a. [B_AX . {} |~ a --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
B_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

let tm = `!a. [B_AX . {} |~ a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
B_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

needs "Library/iter.ml";;

let tm = `!a. [B_AX . {} |~ a --> ITER 4 (Box) a]`;;
let tm = run_conv (TOP_SWEEP_CONV num_CONV THENC REWRITE_CONV[ITER]) tm;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
time (B_HOLMS_CERTIFY_COUNTERMODEL ctm) tm;;   (* CPU time (user): 0.926455 *)
