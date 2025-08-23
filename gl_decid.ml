(* ========================================================================= *)
(* Decision procedure for the provability logic GL.                          *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let HOLDS_BOX_EQ = prove
 (`!W R p w:A.
     (W,R) IN ITF /\ w IN W
     ==> (holds (W,R) V (Box p) w <=>
          (!y. y IN W /\ R w y ==> holds (W,R) V (Box p --> p) y))`,
  INTRO_TAC "!W R p w; WR w" THEN REWRITE_TAC[holds] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  CLAIM_TAC "tnt" `(W:A->bool,R) IN TRANSNT` THENL
  [MATCH_MP_TAC (REWRITE_RULE [SUBSET] ITF_SUBSET_TRANSNT) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC
    (REWRITE_RULE [valid; FORALL_PAIR_THM; IN_TRANSNT_DEF; TRANSITIVE;
                   IN_FRAME; holds_in; holds; RIGHT_IMP_FORALL_THM; IMP_IMP]
                  LOB_THM_TRANSNT) THEN
  EXISTS_TAC `w:A` THEN
  HYP_TAC "tnt" (REWRITE_RULE[IN_TRANSNT_DEF; TRANSITIVE; IN_FRAME]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MATCH_BOX_RIGHT_MODIFIED_TAC : tactic =
  let HOLDS_RIGHT_BOX_MODIFIED = prove
   (`!W:W->bool R.
       (W,R) IN ITF
       ==> !p w. w IN W /\
                 (!y. y IN W /\ R w y /\ holds (W,R) V (Box p) y
                      ==> holds (W,R) V p y)
                 ==> holds (W,R) V (Box p) w`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[HOLDS_BOX_EQ] THEN
    REWRITE_TAC[holds] THEN MESON_TAC[]) in
  let HOLDS_RIGHT_BOX_MODIFIED_ALT = prove
   (`!W:W->bool R.
       (W,R) IN ITF
       ==> !Q p w. w IN W /\
                   (!y. y IN W /\ R w y /\ holds (W,R) V (Box p) y
                        ==> holds (W,R) V p y \/ Q)
                   ==> holds (W,R) V (Box p) w \/ Q`,
    MESON_TAC[HOLDS_RIGHT_BOX_MODIFIED]) in
  let itf_inst = C MATCH_MP (ASSUME `(W:num->bool,R) IN ITF`) in
  let HOLDS_RIGHT_BOX_MODIFIED = itf_inst HOLDS_RIGHT_BOX_MODIFIED
  and HOLDS_RIGHT_BOX_MODIFIED_ALT = itf_inst HOLDS_RIGHT_BOX_MODIFIED_ALT in
  (MATCH_MP_TAC HOLDS_RIGHT_BOX_MODIFIED ORELSE
   MATCH_MP_TAC HOLDS_RIGHT_BOX_MODIFIED_ALT) THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; GEN_TAC];;

let IN_ITF_CLAUSES = prove
 (`!W:W->bool R.
     (W,R) IN ITF
     ==> (!x y z. R y z ==> R x y ==> R x z) /\
         (!w w'. R w w'
                 ==> !p. holds (W,R) V (Box p) w ==> holds (W,R) V p w') /\
         (!w p. holds (W,R) V (Box p) w
                 ==> !w'. R w w' ==> holds (W,R) V p w')`,
  REWRITE_TAC[IN_ITF_DEF; IN_FINITE_FRAME; TRANSITIVE] THEN
  MESON_TAC[HOLDS_LEFT_BOX]);;

let GL_COMPLETENESS_NUM =
 let GL_COMPLETENESS_THEOREM_NUM =
   REWRITE_RULE[num_INFINITE]
     (INST_TYPE [`:num`,`:A`] GL_COMPLETENESS_THM_GEN) in
 prove
 (`!p. (!W:num->bool R.
          (W,R) IN ITF
          ==> !V w. w IN W ==> holds (W,R) V p w)
       ==> [GL_AX . {} |~ p]`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC GL_COMPLETENESS_THEOREM_NUM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in] THEN
  INTRO_TAC "![W] [R]; rf" THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[IN_ITF_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Top-level invocation.                                                     *)
(* ------------------------------------------------------------------------- *)

let IN_ITF_RULES =
  let tm = `(W:num->bool,R) IN ITF` in
  let th = MATCH_MP IN_ITF_CLAUSES (ASSUME tm) in
  CONJUNCTS th;;

let GL_TAC : tactic =
  GEN_HOLMS_TAC MATCH_BOX_RIGHT_MODIFIED_TAC GL_COMPLETENESS_NUM IN_ITF_RULES;;

holms_register_tactic `GL_AX` GL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*
let PREPARE_TAC = HOLMS_PREPARE_TAC GL_COMPLETENESS_NUM;;
let SATURATE_TAC = HOLMS_SATURATE_TAC IN_ITF_RULES;;
let STEP_TAC = HOLMS_STEP_TAC (MATCH_BOX_RIGHT_MODIFIED_TAC,SATURATE_TAC);;
let INNER_TAC = INNER_HOLMS_TAC (MATCH_BOX_RIGHT_MODIFIED_TAC,SATURATE_TAC);;
let box_right_tac = BOX_RIGHT_THEN (MATCH_BOX_RIGHT_MODIFIED_TAC,SATURATE_TAC);;
let right_tac = HOLMS_RIGHT_TAC SATURATE_TAC;;
*)

(* g `[GL_AX . {} |~ Box (Box p --> p) --> Box p]`;; *)
g `!a. [GL_AX . {} |~ Box a --> Box Box a]`;;
e GL_TAC;;
top_thm();;

(* ------------------------------------------------------------------------- *)
(* Countermodels.                                                            *)
(* ------------------------------------------------------------------------- *)

let GL_HOLMS_CERTIFY_COUNTERMODEL : term -> term -> thm =
  let ltm = `ITF:(num->bool)#(num->num->bool)->bool` in
  fun ctm tm ->
    let fm = rand (snd (strip_forall tm))
    and eth = mk_countermodel_existence_thm ctm in
    prove (mk_not_valid_ptm ltm fm,
           CERTIFY_COUNTERMODEL_TAC eth);;

(* ------------------------------------------------------------------------- *)
(* Löb axiom.                                                                *)
(* ------------------------------------------------------------------------- *)

HOLMS_RULE `[GL_AX . {} |~ Box (Box p --> p) --> Box p]`;;

(* ------------------------------------------------------------------------- *)
(* Non-axiom examples.                                                       *)
(* ------------------------------------------------------------------------- *)

(* T_AX *)
let tm = `!a. [GL_AX . {} |~ Box a --> a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
GL_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* K4_AX *)
HOLMS_RULE `!a. [GL_AX . {} |~ Box a --> Box Box a]`;;

(* GL_AX *)
let tm = `!a. [GL_AX . {} |~ a --> Box Diam a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
GL_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* S5_AX *)
let tm = `!a. [GL_AX . {} |~ Diam a --> Box Diam  a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
GL_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

(* GL_AX *)
HOLMS_RULE `!a. [GL_AX . {} |~ Box (Box a --> a) --> Box a]`;;

(* ------------------------------------------------------------------------- *)
(* Furter examples.                                                          *)
(* ------------------------------------------------------------------------- *)

let tm = `!a. [GL_AX . {} |~ a --> Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
GL_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

let tm = `!a. [GL_AX . {} |~ a --> Box Box a]`;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
GL_HOLMS_CERTIFY_COUNTERMODEL ctm tm;;

needs "Library/iter.ml";;

let run_conv conv tm = rhs (concl (conv tm));;
let tm = `!a. [GL_AX . {} |~ a --> ITER 5 (Box) a]`;;
let tm = run_conv (TOP_SWEEP_CONV num_CONV THENC REWRITE_CONV [ITER]) tm;;
let ctm = HOLMS_BUILD_COUNTERMODEL tm;;
time (GL_HOLMS_CERTIFY_COUNTERMODEL ctm) tm;;   (* CPU time (user): 0.93915 *)
