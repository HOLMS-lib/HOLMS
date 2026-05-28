(* ========================================================================= *)
(* Axiom of dependent choice.                                                *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2026.                                  *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/card.ml";;

let NEXT_DEF = new_definition
  `NEXT R (x:A) = @y:B. R x y`;;

let NEXT = prove
 (`!R x:A. R x (NEXT R x) <=> ?y:B. R x y`,
  REWRITE_TAC[NEXT_DEF] THEN MESON_TAC[]);;

let DEPENDENT_CHOICE = prove
 (`!R. (!x:A. x IN fld R ==> ?y. R x y) /\ ~(fld R = {})
       ==> ?f:num->A. !i. R (f i) (f (SUC i))`,
  INTRO_TAC "!R; R fdl" THEN CLAIM_TAC "@x0. x0" `?x0:A. x0 IN fld R` THENL
  [HYP MESON_TAC "fdl" [MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  ABBREV_TAC `f i = ITER i (NEXT R) x0:A` THEN POP_ASSUM (LABEL_TAC "f") THEN
  CLAIM_TAC "f0 f1" `f 0 = x0:A /\ !i. f (SUC i) = NEXT R (f i)` THENL
  [REMOVE_THEN "f" (fun th -> REWRITE_TAC[GSYM th; ITER]); ALL_TAC] THEN
  EXISTS_TAC `f:num->A` THEN INDUCT_TAC THENL
  [HYP REWRITE_TAC "f0 f1 x0" [NEXT] THEN HYP MESON_TAC "R x0" [];
   ALL_TAC] THEN
  POP_ASSUM (LABEL_TAC "ind") THEN
  REMOVE_THEN "f1" (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
  REWRITE_TAC[NEXT] THEN HYP MESON_TAC "R ind" [IN_FLD]);;
