(* ========================================================================= *)
(* Some tests.                                                               *)
(*                                                                           *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Tests and examples for the modal logic K.                                 *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE `[{} . {} |~ Box (a && b) <-> Box a && Box b]`;;

time HOLMS_RULE `[{} . {} |~ Box a || Box b --> Box (a || b)]`;;

time HOLMS_BUILD_COUNTERMODEL `[{} . {} |~ Box a --> a]`;;

time HOLMS_BUILD_COUNTERMODEL `[{} . {} |~ Box (a || b) --> Box a || Box b]`;;

time HOLMS_BUILD_COUNTERMODEL `[{} . {} |~ Box (Box a --> Diam a)]`;;

(* Löb schema. *)
time HOLMS_BUILD_COUNTERMODEL `[{} . {} |~ Box (Box a --> a) --> Box a]`;;

(* ------------------------------------------------------------------------- *)
(* Tests and examples for the modal logic T.                                 *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE `[T_AX . {} |~ Box (a && b) <-> Box a && Box b]`;;

time HOLMS_RULE `[T_AX . {} |~ Box a || Box b --> Box (a || b)]`;;

time HOLMS_RULE `[T_AX . {} |~ Box a --> a]`;;

time HOLMS_RULE `[T_AX . {} |~ Box Box a --> Diam a]`;;

time HOLMS_RULE `[T_AX . {} |~ Box (Box a --> Diam a)]`;;

time HOLMS_RULE `[T_AX . {} |~ a --> Diam a]`;;

time HOLMS_RULE `[T_AX . {} |~ Box a --> Diam a]`;;

time HOLMS_BUILD_COUNTERMODEL `[T_AX . {} |~ Diam a --> a]`;;

time HOLMS_BUILD_COUNTERMODEL `[T_AX . {} |~ Box a --> Box Box a]`;;

(* Löb schema. *)
time HOLMS_BUILD_COUNTERMODEL `[T_AX . {} |~ Box (Box a --> a) --> Box a]`;;

(* ------------------------------------------------------------------------- *)
(* Tests and examples for the modal logic K4.                                *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE `[K4_AX . {} |~ Box (a && b) <-> Box a && Box b]`;;

time HOLMS_RULE `[K4_AX . {} |~ Box a || Box b --> Box (a || b)]`;;

time HOLMS_RULE `[K4_AX . {} |~ Box a --> Box Box a]`;;

time HOLMS_RULE `[K4_AX . {} |~ Dotbox (Box a) <-> Box a]`;;

time HOLMS_RULE `[K4_AX . {} |~ Dotbox (Dotbox a) <-> Dotbox a]`;;

time HOLMS_BUILD_COUNTERMODEL `[K4_AX . {} |~ Box a --> a]`;;

(* Löb schema. *)
(* HOLMS_BUILD_COUNTERMODEL `[K4_AX . {} |~ Box (Box a --> a) --> Box a]`;; *)

(* ------------------------------------------------------------------------- *)
(* Tests and examples for the modal logic GL.                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Some arithmetical principles investigated via provability in GL           *)
(*                                                                           *)
(* Modal formulas can be realised as sentences (i.e. closed formulas) of     *)
(* Peano Arithmetic (PA). The Box is thus interpreted as the predicate of    *)
(* formal provability in PA, Bew(x).                                         *)
(*                                                                           *)
(* Under this interpretation, we will read modal formulas as follows:        *)
(* - Box p = p is provable in PA;                                            *)
(* - Not (Box (Not p)) = p is consistent with PA                             *)
(* - Not (Box p) = p is unprovable in PA                                     *)
(* - Box (Not p) = p is refutable in PA                                      *)
(* - (Box p) || (Box (Not p)) = p is decidable in PA                         *)
(* - Not (Box p) && Not (Box (Not p)) = p is undecidable in PA               *)
(* - Box (p <-> q) = p and q are equivalent over PA                          *)
(* - Box (False) = PA is inconsistent                                        *)
(* - Not (Box False) = Diam True = PA is consistent                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Löb schema.                                                               *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE `!a. [GL_AX . {} |~ Box (Box a --> a) --> Box a]`;;

(* ------------------------------------------------------------------------- *)
(* Formalised Second Incompleteness Theorem:                                 *)
(* In PA, the following is provable: If PA is consistent, it cannot prove    *)
(* its own consistency                                                       *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `[GL_AX . {} |~ Not (Box False) --> Not (Box (Diam True))]`;;

(* ------------------------------------------------------------------------- *)
(* PA ignores unprovability statements.                                      *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `!p. [GL_AX . {} |~ Box False <-> Box Diam p]`;;

(* ------------------------------------------------------------------------- *)
(* If PA does not prove its inconsistency, then its consistency is           *)
(* undecidable.                                                              *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `[GL_AX . {} |~ Not (Box (Box False))
                  --> Not (Box (Not (Box False))) &&
                      Not (Box (Not (Not (Box False))))]`;;

(* ------------------------------------------------------------------------- *)
(* If a sentence is equivalent to its own unprovability, and if PA does not  *)
(* prove its inconsistency, then that sentence is undecidable.               *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) && Not (Box (Box False))
                      --> Not (Box p) && Not (Box (Not p))]`;;

(* ------------------------------------------------------------------------- *)
(* If a reflection principle implies the second iterated consistency         *)
(*   assertion, then the converse implication holds too.                     *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `!p. [GL_AX . {} |~ Box ((Box p --> p) --> Diam (Diam True))
                      --> (Diam (Diam True) --> (Box p --> p))]`;;

(* ------------------------------------------------------------------------- *)
(* A Godel sentence is equiconsistent with a consistency statement           *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) <->
                      Box (p <-> Not (Box False))]`;;

(* ------------------------------------------------------------------------- *)
(* For any arithmetical sentences p q, p is equivalent to unprovability      *)
(* of q --> p iff p is equivalent to consistency of q                        *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `!p q. [GL_AX . {} |~ Dotbox (p <-> Not Box (q --> p)) <->
                        Dotbox (p <-> Diam q)]`;;

(* ------------------------------------------------------------------------- *)
(* Valid in GL but not in K.                                                 *)
(* ------------------------------------------------------------------------- *)

time HOLMS_RULE
  `!a. [GL_AX . {} |~ Box Diam Box Diam a <-> Box Diam a]`;;

(* Countermodel is not tree-like. *)
(* time HOLMS_BUILD_COUNTERMODEL
  `!a. [K4_AX . {} |~ Box Diam Box Diam a <-> Box Diam a]`;; *)

(* ------------------------------------------------------------------------- *)
(* Example of countermodel.                                                  *)
(* There exists an arithmetical sentece p such that it is consistent with PA *)
(* that both p is undecidable and it is provable that p is decidable         *)
(* ------------------------------------------------------------------------- *)

time HOLMS_BUILD_COUNTERMODEL
  `[GL_AX . {} |~ Box (Box p || Box Not p) --> Box p || Box Not p]`;;

(* ------------------------------------------------------------------------- *)
(* Basic tests.                                                              *)
(* ------------------------------------------------------------------------- *)

(* CPU time (user): 1.41848.  Was 7.413296 *)
let test_prove tm =
  try prove(tm,HOLMS_TAC) with Failure _ -> failwith (string_of_term tm)
in
time (map test_prove)
 [`[GL_AX . {}
    |~ Not Box p && Box (Box p --> p)
       --> Diam (Not p && Box p && (Box p --> p) && Box (Box p --> p))]`;
  `[GL_AX . {}
    |~ Box (q <-> (Box q --> p)) --> Box (Box p --> p) --> Box p]`;
  `[GL_AX . {} |~ Box (Box p --> p) <-> Box p]`;
  `[GL_AX . {} |~ Dotbox Box p <-> Box p]`;
  `[GL_AX . {} |~ Dotbox Box p <-> Box Dotbox p]`;
  `[GL_AX . {} |~ Dotbox p <-> Dotbox Dotbox p]`;
  `[GL_AX . {} |~ Diam p && Box q --> Diam (p && q)]`;
  `[GL_AX . {} |~ Box (p && q) --> Box p && Box q]`;
  `[GL_AX . {} |~ Box (Box p --> p) <-> Box (Box p && p)]`;
  `[GL_AX . {} |~ Box Diam False --> Box False]`;
  `[GL_AX . {} |~ Box (p <-> Box p) <-> Box (p <-> True)]`;
  `[GL_AX . {} |~ Box (p <-> Box p) --> Box (p <-> True)]`;
  `[GL_AX . {} |~ Box (p <-> True) --> Box (p <-> Box p)]`;
  `[GL_AX . {} |~ Box (p <-> Not (Box p)) <-> Box (p <-> Not (Box False))]`;
  `[GL_AX . {} |~ Box (p <-> Box (Not p)) <-> Box (p <-> (Box False))]`;
  `[GL_AX . {} |~ Box (p <-> Not (Box (Not p))) <-> Box (p <-> False)]`;
  `[GL_AX . {}
    |~ Box ((Box p --> p) --> Not Box Box False) -->  Box Box False]`];;

(* ------------------------------------------------------------------------- *)
(* Further tests.                                                            *)
(* ------------------------------------------------------------------------- *)

(* CPU time (user): 3.642329.  Was 19.381427 *)
let gl_theorems =
 [("GL_Godel_sentence_equiconsistent_consistency",
   `Box (p <-> Not Box p) <-> Box (p <-> Not Box False)`);
  ("GL_PA_ignorance", `Box False <-> Box Diam p`);
  ("GL_PA_undecidability_of_consistency",
   `Not Box Box False --> Not Box Not Box False && Not Box Not Not Box False`);
  ("GL_and_assoc_th", `(p && q) && r <-> p && q && r`);
  ("GL_and_comm_th", `p && q <-> q && p`);
  ("GL_and_left_th", `p && q --> p`);
  ("GL_and_left_true_th", `True && p <-> p`);
  ("GL_and_or_ldistrib_th", `p && (q || r) <-> p && q || p && r`);
  ("GL_and_pair_th", `p --> q --> p && q`);
  ("GL_and_right_th", `p && q --> q`);
  ("GL_and_rigth_true_th", `p && True <-> p`);
  ("GL_and_subst_left_th", `(p1 <-> p2) --> (p1 && q <-> p2 && q)`);
  ("GL_and_subst_right_th", `(q1 <-> q2) --> (p && q1 <-> p && q2)`);
  ("GL_arithmetical_fixpoint",
   `Dotbox (p <-> Not Box (q --> p)) <-> Dotbox (p <-> Diam q)`);
  ("GL_axiom_addimp", `p --> q --> p`);
  ("GL_axiom_and", `p && q <-> (p --> q --> False) --> False`);
  ("GL_axiom_boximp", `Box (p --> q) --> Box p --> Box q`);
  ("GL_axiom_distribimp", `(p --> q --> r) --> (p --> q) --> p --> r`);
  ("GL_axiom_doubleneg", `((p --> False) --> False) --> p`);
  ("GL_axiom_iffimp1", `(p <-> q) --> p --> q`);
  ("GL_axiom_iffimp2", `(p <-> q) --> q --> p`);
  ("GL_axiom_impiff", `(p --> q) --> (q --> p) --> (p <-> q)`);
  ("GL_axiom_lob", `Box (Box p --> p) --> Box p`);
  ("GL_axiom_not", `Not p <-> p --> False`);
  ("GL_axiom_or", `p || q <-> Not (Not p && Not q)`);
  ("GL_axiom_true", `True <-> False --> False`);
  ("GL_box_and_inv_th", `Box p && Box q --> Box (p && q)`);
  ("GL_box_and_th", `Box (p && q) --> Box p && Box q`);
  ("GL_box_iff_th", `Box (p <-> q) --> (Box p <-> Box q)`);
  ("GL_contrapos_eq_th", `p --> q <-> Not q --> Not p`);
  ("GL_contrapos_th", `(p --> q) --> Not q --> Not p`);
  ("GL_crysippus_th", `Not (p --> q) <-> p && Not q`);
  ("GL_de_morgan_and_th", `Not (p && q) <-> Not p || Not q`);
  ("GL_de_morgan_or_th", `Not (p || q) <-> Not p && Not q`);
  ("GL_dot_box", `Box p --> Box p && Box Box p`);
  ("GL_ex_falso_th", `False --> p`);
  ("GL_iff_def_th", `(p <-> q) <-> (p --> q) && (q --> p)`);
  ("GL_iff_refl_th", `p <-> p`);
  ("GL_iff_sym_th", `(p <-> q) --> (q <-> p)`);
  ("GL_imp_contr_th", `(p --> False) --> p --> q`);
  ("GL_imp_mono_th", `(p' --> p) && (q --> q') --> (p --> q) --> p' --> q'`);
  ("GL_imp_refl_th", `p --> p`);
  ("GL_imp_swap_th", `(p --> q --> r) --> q --> p --> r`);
  ("GL_imp_trans_th", `(q --> r) --> (p --> q) --> p --> r`);
  ("GL_imp_truefalse_th", `(q --> False) --> p --> (p --> q) --> False`);
  ("GL_modusponens_th", `(p --> q) && p --> q`);
  ("GL_nc_th", `p && Not p --> False`);
  ("GL_not_not_false_th", `(p --> False) --> False <-> p`);
  ("GL_not_not_th", `Not Not p <-> p`);
  ("GL_not_true_th", `Not True <-> False`);
  ("GL_or_assoc_left_th", `p || q || r --> (p || q) || r`);
  ("GL_or_assoc_right_th", `(p || q) || r --> p || q || r`);
  ("GL_or_assoc_th", `p || q || r <-> (p || q) || r`);
  ("GL_or_left_th", `q --> p || q`); ("GL_or_lid_th", `False || p <-> p`);
  ("GL_or_rid_th", `p || False <-> p`); ("GL_or_right_th", `p --> p || q`);
  ("GL_reflection_and_iterated_consistency",
   `Box ((Box p --> p) --> Diam Diam True) -->
    Diam Diam True -->
    Box p -->
    p`);
  ("GL_schema_4", `Box p --> Box Box p`);
  ("GL_second_incompleteness_theorem",
   `Not Box False --> Not Box Diam True`);
  ("GL_tnd_th", `p || Not p`); ("GL_truth_th", `True`);
  ("GL_undecidability_of_Godels_formula",
   `Box (p <-> Not Box p) && Not Box Box False -->
    Not Box p && Not Box Not p`);
  ("GL_undecidability_of_godels_formula",
   `Box (p <-> Not Box p) && Not Box Box False -->
    Not Box p && Not Box Not p`)] in
let test_prove (s,tm) =
  let th = try HOLMS_RULE (mk_comb(`MODPROVES GL_AX {}`,tm))
           with Failure _ -> failwith s in
  s,th in
time (map test_prove) gl_theorems;;

(* CPU time (user): 7.117629.  Was 47.994603. *)
time HOLMS_RULE
  `[GL_AX . {}
    |~ Dotbox (p <-> (q && (Box (p --> q) --> Box Not p))) <->
       Dotbox (p <-> (q && Box Not q))]`;;

(* CPU time (user): 166.020036 (about 3min).  Was 896.120732 (about 15 min). *)
time HOLMS_RULE
  `[GL_AX . {}
    |~ Dotbox (p <-> (Diam p --> q && Not Box (p --> q))) <->
       Dotbox (p <-> (Diam True --> q && Not Box (Box False --> q)))]`;;

(* ------------------------------------------------------------------------- *)
(* Further examples of countermodels.                                        *)
(* ------------------------------------------------------------------------- *)

(* Countermodel is not tree-like. *)
(* time HOLMS_BUILD_COUNTERMODEL
  `[K4_AX . {}
    |~ Dotbox (p <-> (q && (Box (p --> q) --> Box Not p))) <->
       Dotbox (p <-> (q && Box Not q))]`;; *)
