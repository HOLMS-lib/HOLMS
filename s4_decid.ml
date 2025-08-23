(* ========================================================================= *)
(* Decision procedure for the modal logic S4.                                *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let IN_RTF_CLAUSES = prove
 (`!W:W->bool R.
     (W,R) IN RTF
     ==> (!x. x IN W ==> R x x) /\
         (!x y z. R y z ==> R x y ==> R x z) /\
         (!w w'. R w w'
                 ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
         (!w p. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w')`,
  REWRITE_TAC[IN_RTF_DEF; IN_FINITE_FRAME; REFLEXIVE; TRANSITIVE] THEN
  MESON_TAC[HOLDS_LEFT_BOX]);;

let S4_COMPLETENESS_NUM =
 let S4_COMPLETENESS_THEOREM_NUM =
   REWRITE_RULE[num_INFINITE]
     (INST_TYPE [`:num`,`:A`] S4_COMPLETENESS_THM_GEN) in
 prove
 (`!p. (!W:num->bool R.
          (W,R) IN RTF
          ==> !V w. w IN W /\ R w w ==> holds (W,R) V p w)
       ==> [S4_AX . {} |~ p]`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC S4_COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN
  INTRO_TAC "![W] [R]; rf" THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[IN_RTF_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let IN_RTF_RULES =
  let tm = `(W:num->bool,R) IN RTF` in
  let th = MATCH_MP IN_RTF_CLAUSES (ASSUME tm) in
  CONJUNCTS th;;

let S4_TAC : tactic =
  GEN_HOLMS_TAC MATCH_BOX_RIGHT_TAC S4_COMPLETENESS_NUM IN_RTF_RULES;;

holms_register_tactic `S4_AX` S4_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*
let PREPARE_TAC = HOLMS_PREPARE_TAC S4_COMPLETENESS_NUM;;
let SATURATE_TAC = HOLMS_SATURATE_TAC IN_RTF_RULES;;
let STEP_TAC = HOLMS_STEP_TAC SATURATE_TAC;;
let INNER_TAC = INNER_HOLMS_TAC SATURATE_TAC;;
let box_right_tac = BOX_RIGHT_THEN SATURATE_TAC;;
let right_tac = HOLMS_RIGHS4_TAC SATURATE_TAC;;
*)

g `[S4_AX . {} |~ Box (Atom a && Atom b) <->
                  Box Atom a && Box Atom b]`;;
e S4_TAC;;
top_thm();;

(* ------------------------------------------------------------------------- *)
(* Countermodels.                                                            *)
(* ------------------------------------------------------------------------- *)

let S4_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `TF:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

(* ------------------------------------------------------------------------- *)
(* Experiments.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Axioms *)
HOLMS_RULE `!a. [S4_AX . {} |~ Box a --> Box Box a]`;;

(* ------------------------------------------------------------------------- *)
(* Non-axiom examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* T_AX *)
let tm = `!a. [{} . {} |~ Box a --> a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* B_AX *)
let tm = `!a. [{} . {} |~ a --> Box Diam a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* S5_AX *)
let tm = `!a. [{} . {} |~ Diam a --> Box Diam  a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* GL_AX *)
(* 
let tm = `!a. [{} . {} |~ Box (Box a --> a) --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;
*)

(* ------------------------------------------------------------------------- *)
(* Simple examples.                                                          *)
(* ------------------------------------------------------------------------- *)

let tm = `!a. [S4_AX . {} |~ a --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

let tm = `!a. [S4_AX . {} |~ a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

needs "Library/iter.ml";;

let run_conv conv tm = rhs (concl (conv tm));;
let tm = `!a. [S4_AX . {} |~ a --> ITER 5 (Box) a]`;;
let tm = run_conv (TOP_SWEEP_CONV num_CONV THENC REWRITE_CONV [ITER]) tm;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
time (S4_HOLMS_CERTIFY_COUNTERMODEL ctm) tm;;   (* CPU time (user): 0.657422 *)

(* ------------------------------------------------------------------------- *)
(* Experiments.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Axioms *)
HOLMS_RULE `!a. [S4_AX . {} |~ Box a --> Box Box a]`;;
HOLMS_RULE `!a. [S4_AX . {} |~ Box a --> a]`;;

HOLMS_RULE `[S4_AX . {} |~ Box (Atom a && Atom b) <->
                           Box Atom a && Box Atom b]`;;

g `[S4_AX . {} |~ Box (Atom a && Atom b) <->
                  Box Atom a && Box Atom b]`;;
e S4_TAC;;
top_thm();;

(* ------------------------------------------------------------------------- *)
(* Countermodels.                                                            *)
(* ------------------------------------------------------------------------- *)

let S4_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `RTF:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

(* ------------------------------------------------------------------------- *)
(* Non-axiom examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* T_AX *)
HOLMS_RULE `!a. [S4_AX . {} |~ Box a --> a]`;;

(* B_AX *)
let tm = `!a. [S4_AX . {} |~ a --> Box Diam a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* S5_AX *)
let tm = `!a. [S4_AX . {} |~ Diam a --> Box Diam  a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* GL_AX *)
(* let tm = `!a. [S4_AX . {} |~ Box (Box a --> a) --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;; *)

(* ------------------------------------------------------------------------- *)
(* Further examples.                                                         *)
(* ------------------------------------------------------------------------- *)

let tm = `!a. [S4_AX . {} |~ a --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

let tm = `!a. [S4_AX . {} |~ a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
S4_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

needs "Library/iter.ml";;

let run_conv conv tm = rhs (concl (conv tm));;
let tm = `!a. [S4_AX . {} |~ a --> ITER 4 (Box) a]`;;
let tm = run_conv (TOP_SWEEP_CONV num_CONV THENC REWRITE_CONV[ITER]) tm;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
time (S4_HOLMS_CERTIFY_COUNTERMODEL ctm) tm;;   (* CPU time (user): 1.022659 *)
