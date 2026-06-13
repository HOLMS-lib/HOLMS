(* ========================================================================= *)
(* HOL-Light Library for Modal Systems                                       *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi 2025-2026.                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Libraries.                                                                *)
(* ------------------------------------------------------------------------- *)

needs "Library/card.ml";;                    (* Cardinality                 *)
needs "Library/rstc.ml";;                    (* Refl, sym, trans closure    *)
loadt "HOLMS/dep_choice.ml";;                (* Axiom of dependent choice   *)

(* ------------------------------------------------------------------------- *)
(* Syntax, semantics and calculus.                                           *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/misc.ml";;                      (* Miscellanea                 *)
loadt "HOLMS/proofflow.ml";;                 (* Further proof-flow tactics  *)
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

loadt "HOLMS/setconsistent.ml";;            (* Consistent sets of formulae  *)
loadt "HOLMS/conjlist.ml";;                 (* Iterated conjunctions        *)
loadt "HOLMS/consistent.ml";;               (* Consistent lists of formulae *)
loadt "HOLMS/gen_completeness.ml";;         (* Lemmata about completeness   *)

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
loadt "HOLMS/d_completeness.ml";;

(* ------------------------------------------------------------------------- *)
(* General tools for decidability and countermodel generation.               *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/gen_decid.ml";;                 (* Decision procedures          *)
loadt "HOLMS/gen_countermodel.ml";;          (* Countermodel construction    *)

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

loadt "HOLMS/tests.ml";;                     (* Tests for these logics       *)

(* ------------------------------------------------------------------------- *)
(* Grzegorczyk Logic (GRZ): Meta-theory, translations to GL,                 *)
(* decision procedure (via translation to GL).                               *)
(* ------------------------------------------------------------------------- *)

loadt "HOLMS/wwf.ml";;                  (* Weakly wellfoundness              *)
loadt "HOLMS/translations.ml";;         (* Splitting Translation             *)
loadt "HOLMS/grz_modular.ml";;          (* Grz with Modular Completeness     *) 
(*loadt "HOLMS/grz_boolos.ml";;*)       (* Grz with Boolos Completeness      *)
loadt "HOLMS/grz_tests.ml";;            (* Tests for Grz                     *)
loadt "HOLMS/god_transl.ml";;           (* Godel-McKinsey-Tarski Translation *)