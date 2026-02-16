(* ========================================================================= *)
(* HOL-Light Library for Modal Systems                                       *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Libraries.                                                                *)
(* ------------------------------------------------------------------------- *)

needs "Library/card.ml";;                    (* Cardinality                 *)
needs "Library/rstc.ml";;                    (* Refl, sym, trans closure    *)

(* ------------------------------------------------------------------------- *)
(* Syntax, semantics and calculus.                                           *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/misc.ml";;                      (* Miscellanea                 *)
loadt "HOLMS/modal.ml";;                     (* Syntax and semantics        *)
loadt "HOLMS/calculus.ml";;                  (* Axiomatic calculus          *)

(* ------------------------------------------------------------------------- *)
(* Correspondence Theory.                                                    *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/parametric_correspondence.ml";;   (* Parametric code            *)
loadt "HOLMS/ad_hoc_correspondence.ml";;       (* Ad hoc polimorphic code    *)

(* ------------------------------------------------------------------------- *)
(* Meta-theory.                                                              *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/conjlist.ml";;                  (* Iterated conjunctions       *)
loadt "HOLMS/consistent.ml";;                (* Consistent sets of formulae *)
loadt "HOLMS/gen_completeness.ml";;          (* Lemmata about completeness  *)

(* ------------------------------------------------------------------------- *)
(* Soundness and completeness results specific to each logic.                *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/k_completeness.ml";;
loadt "HOLMS/t_completeness.ml";;
loadt "HOLMS/k4_completeness.ml";;
loadt "HOLMS/s4_completeness.ml";;
loadt "HOLMS/b_completeness.ml";;
loadt "HOLMS/s5_completeness.ml";;
loadt "HOLMS/gl_completeness.ml";;

(* ------------------------------------------------------------------------- *)
(* General tools for decidability and countermodel generation.               *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/gen_decid.ml";;
loadt "HOLMS/gen_countermodel.ml";;

(* ------------------------------------------------------------------------- *)
(* Decision procedures and countermodel generators specific to each logic.   *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/k_decid.ml";;
loadt "HOLMS/t_decid.ml";;
loadt "HOLMS/k4_decid.ml";;
loadt "HOLMS/s4_decid.ml";;
loadt "HOLMS/b_decid.ml";;
loadt "HOLMS/s5_decid.ml";;
loadt "HOLMS/gl_decid.ml";;

(* ------------------------------------------------------------------------- *)
(* Grzegorczyk Logic (GRZ): Meta-theory, translations to GL,                 *)
(* decision procedure (via translation to GL).                               *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/translations.ml";;
loadt "HOLMS/grz.ml";;
loadt "HOLMS/grz_tests.ml";;
loadt "HOLMS/god_transl.ml";;
