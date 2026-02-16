(* ========================================================================= *)
(* Axiomatic of the modal provability logic GL.                              *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* (c) Copyright, Antonella Bilotta, Marco Maggesi,                          *)
(*                Cosimo Perini Brogi, Leonardo Quartini 2024.               *)
(*                                                                           *)
(* The initial part of this code has been adapted from the proof of the      *)
(* Godel incompleteness theorems formalized by John Harrison, distributed    *)
(* with HOL Light in the subdirectory Arithmetic.                            *)
(* ========================================================================= *)

needs "HOLMS/modal.ml";;

(* ------------------------------------------------------------------------- *)
(* Concrete syntax for judgements: `[S . H |~ p]`.                           *)
(*   - S set of axioms / axiom schemas;                                      *)
(*   - H set of hypothesis;                                                  *)
(*   - p conclusion.                                                         *)
(* ------------------------------------------------------------------------- *)

reserve_words["|~"];;

let modal_judgment_parser =
  let ktm = Varp("MODPROVES",dpty) in
  let par = (a (Resword "[") ++ parse_preterm >> snd) ++
            (a (Resword ".") ++ parse_preterm >> snd) ++
            (a (Resword "|~") ++ parse_preterm >> snd) ++
            a (Resword "]") >> fst in
  fun inp ->
    let ((s,h),p),rest = par inp in
    let ptm = Combp(Combp(Combp(ktm,s),h),p) in
    ptm,rest;;

install_parser("modal_judgment",modal_judgment_parser);;

let modal_judgement_printer (fmt:formatter) (tm:term) : unit =
  match tm with
  | Comb(Comb(Comb(Const("MODPROVES",_),stm),htm),ptm) ->
    pp_open_box fmt 1; pp_print_string fmt "[";
    pp_open_box fmt 0; pp_print_term fmt stm;
    pp_print_space fmt ();
    pp_print_string fmt ". ";
    pp_print_term fmt htm;
    pp_print_space fmt ();
    pp_print_string fmt "|~ ";
    pp_print_term fmt ptm;
    pp_close_box fmt ();
    pp_print_string fmt "]";
    pp_close_box fmt ()
  | _ -> failwith "modal_judgement_printer";;

install_user_printer("modal_judgement",modal_judgement_printer);;

(* ------------------------------------------------------------------------- *)
(* Axioms of the Modal Logic K.                                              *)
(* ------------------------------------------------------------------------- *)

let KAXIOM_RULES,KAXIOM_INDUCT,KAXIOM_CASES = new_inductive_definition
  `(!p q. KAXIOM (p --> (q --> p))) /\
   (!p q r. KAXIOM ((p --> q --> r) --> (p --> q) --> (p --> r))) /\
   (!p. KAXIOM (((p --> False) --> False) --> p)) /\
   (!p q. KAXIOM ((p <-> q) --> p --> q)) /\
   (!p q. KAXIOM ((p <-> q) --> q --> p)) /\
   (!p q. KAXIOM ((p --> q) --> (q --> p) --> (p <-> q))) /\
   KAXIOM (True <-> False --> False) /\
   (!p. KAXIOM (Not p <-> p --> False)) /\
   (!p q. KAXIOM (p && q <-> (p --> q --> False) --> False)) /\
   (!p q. KAXIOM (p || q <-> Not(Not p && Not q))) /\
   (!p q. KAXIOM (Box (p --> q) --> Box p --> Box q))`;;

(* ------------------------------------------------------------------------- *)
(* Judgments form normal modal logics.                                       *)
(* ------------------------------------------------------------------------- *)

let MODPROVES_RULES,MODPROVES_INDUCT,MODPROVES_CASES =
  new_inductive_definition
  `(!H p. KAXIOM p ==> [S . H |~ p]) /\
   (!H p. p IN S ==> [S . H |~ p]) /\
   (!H p. p IN H ==> [S . H |~ p]) /\
   (!H p q. [S . H |~ p --> q] /\ [S . H |~ p] ==> [S . H |~ q]) /\
   (!H p. [S . {} |~ p] ==> [S . H |~ Box p])`;;

let MODPROVES_INDUCT_STRONG =
  derive_strong_induction(MODPROVES_RULES,MODPROVES_INDUCT);;

(* Test: *)
(*
try_user_printer std_formatter `MODAL_PROVES A H P`;;
*)

(* ------------------------------------------------------------------------- *)
(* The primitive basis, separated into its named components.                 *)
(* ------------------------------------------------------------------------- *)

let MLK_axiom_addimp = prove
 (`!S H p q. [S . H |~ p --> (q --> p)]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_distribimp = prove
 (`!S H p q r. [S . H |~ (p --> q --> r) --> (p --> q) --> (p --> r)]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_doubleneg = prove
 (`!S H p. [S . H |~ ((p --> False) --> False) --> p]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_iffimp1 = prove
 (`!S H p q. [S . H |~ (p <-> q) --> p --> q]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_iffimp2 = prove
 (`!S H p q. [S . H |~ (p <-> q) --> q --> p]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_impiff = prove
 (`!S H p q. [S . H |~ (p --> q) --> (q --> p) --> (p <-> q)]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_true = prove
 (`!S H. [S . H |~ True <-> (False --> False)]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_not = prove
 (`!S H p. [S . H |~ Not p <-> (p --> False)]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_and = prove
 (`!S H p q. [S . H |~ p && q <-> (p --> q --> False) --> False]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_or = prove
 (`!S H p q. [S . H |~ p || q <-> Not(Not p && Not q)]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_axiom_boximp = prove
 (`!S H p q. [S . H |~ Box (p --> q) --> Box p --> Box q]`,
  MESON_TAC[MODPROVES_RULES; KAXIOM_RULES]);;

let MLK_modusponens = prove
 (`!S H p. [S . H |~ p --> q] /\ [S . H |~ p] ==> [S . H |~ q]`,
  MESON_TAC[MODPROVES_RULES]);;

let MLK_necessitation = prove
 (`!S H p. [S . {} |~ p] ==> [S . H |~ Box p]`,
  MESON_TAC[MODPROVES_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity.                                                             *)
(* ------------------------------------------------------------------------- *)

let MODPROVES_INDUCT_STRONG =
  derive_strong_induction(MODPROVES_RULES,MODPROVES_INDUCT);;

let MODPROVES_MONO1 = prove
 (`!S S' H p. S SUBSET S' /\ [S . H |~ p] ==> [S' . H |~ p]`,
  GEN_TAC THEN SUBGOAL_THEN
    `!H p. [S . H |~ p] ==> !S'. S SUBSET S' ==> [S' . H |~ p]`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC MODPROVES_INDUCT THEN
  MESON_TAC[MODPROVES_RULES; SUBSET]);;
g `!S S' H p. S SUBSET S' /\ [S . H |~ p] ==> [S' . H |~ p]`;;
e GEN_TAC;;
e (SUBGOAL_THEN
    `!H p. [S . H |~ p] ==> !S'. S SUBSET S' ==> [S' . H |~ p]`
    (fun th -> MESON_TAC[th]));;
e ( MATCH_MP_TAC MODPROVES_INDUCT);;


let MODPROVES_MONO2 = prove
 (`!S H H' p. [S . H |~ p] /\ H SUBSET H' ==> [S . H' |~ p]`,
  GEN_TAC THEN SUBGOAL_THEN
    `!H p. [S . H |~ p] ==> !H'. H SUBSET H' ==> [S . H' |~ p]`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC MODPROVES_INDUCT_STRONG THEN REWRITE_TAC[SUBSET] THEN
  MESON_TAC[MODPROVES_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Some purely propositional schemas and derived rules.                      *)
(* ------------------------------------------------------------------------- *)

let MLK_iff_imp1 = prove
 (`!p q. [S . H |~ p <-> q] ==> [S . H |~ p --> q]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_iffimp1]);;

let MLK_iff_imp2 = prove
 (`!p q. [S . H |~ p <-> q] ==> [S . H |~ q --> p]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_iffimp2]);;

let MLK_imp_antisym = prove
 (`!p q. [S . H |~ p --> q] /\ [S . H |~ q --> p] ==> [S . H |~ p <-> q]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_impiff]);;

let MLK_add_assum = prove
 (`!p q. [S . H |~ q] ==> [S . H |~ p --> q]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_addimp]);;

let MLK_imp_refl_th = prove
 (`!p. [S . H |~ p --> p]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_distribimp; MLK_axiom_addimp]);;

let MLK_imp_add_assum = prove
 (`!p q r. [S . H |~ q --> r] ==> [S . H |~ (p --> q) --> (p --> r)]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_distribimp; MLK_add_assum]);;

let MLK_imp_unduplicate = prove
 (`!p q. [S . H |~ p --> p --> q] ==> [S . H |~ p --> q]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_distribimp; MLK_imp_refl_th]);;

let MLK_imp_trans = prove
 (`!p q. [S . H |~ p --> q] /\ [S . H |~ q --> r] ==> [S . H |~ p --> r]`,
  MESON_TAC[MLK_modusponens; MLK_imp_add_assum]);;

let MLK_imp_swap = prove
 (`!p q r. [S . H |~ p --> q --> r] ==> [S . H |~ q --> p --> r]`,
  MESON_TAC[MLK_imp_trans; MLK_axiom_addimp; MLK_modusponens;
            MLK_axiom_distribimp]);;

let MLK_imp_trans_chain_2 = prove
 (`!p q1 q2 r.
     [S . H |~ p --> q1] /\ [S . H |~ p --> q2] /\ [S . H |~ q1 --> q2 --> r]
     ==> [S . H |~ p --> r]`,
  ASM_MESON_TAC[MLK_imp_trans; MLK_imp_swap; MLK_imp_unduplicate]);;

let MLK_imp_trans_th = prove
 (`!p q r. [S . H |~ (q --> r) --> (p --> q) --> (p --> r)]`,
  MESON_TAC[MLK_imp_trans; MLK_axiom_addimp; MLK_axiom_distribimp]);;

let GLimp_add_concl = prove
 (`!p q r. [S . H |~ p --> q] ==> [S . H |~ (q --> r) --> (p --> r)]`,
  MESON_TAC[MLK_modusponens; MLK_imp_swap; MLK_imp_trans_th]);;

let MLK_imp_trans2 = prove
 (`!p q r s. [S . H |~ p --> q --> r] /\ [S . H |~ r --> s]
             ==> [S . H |~ p --> q --> s]`,
  MESON_TAC[MLK_imp_add_assum; MLK_modusponens; MLK_imp_trans_th]);;

let MLK_imp_swap_th = prove
 (`!p q r. [S . H |~ (p --> q --> r) --> (q --> p --> r)]`,
  MESON_TAC[MLK_imp_trans; MLK_axiom_distribimp; GLimp_add_concl;
            MLK_axiom_addimp]);;

let MLK_contrapos = prove
 (`!p q. [S . H |~ p --> q] ==> [S . H |~ Not q --> Not p]`,
  MESON_TAC[MLK_imp_trans; MLK_iff_imp1; MLK_axiom_not;
            GLimp_add_concl; MLK_iff_imp2]);;

let MLK_imp_truefalse_th = prove
 (`!p q. [S . H |~ (q --> False) --> p --> (p --> q) --> False]`,
  MESON_TAC[MLK_imp_trans; MLK_imp_trans_th; MLK_imp_swap_th]);;

let MLK_imp_insert = prove
 (`!p q r. [S . H |~ p --> r] ==> [S . H |~ p --> q --> r]`,
  MESON_TAC[MLK_imp_trans; MLK_axiom_addimp]);;

let MLK_imp_mono_th = prove
 (`[S . H |~ (p' --> p) --> (q --> q') --> (p --> q) --> (p' --> q')]`,
  MESON_TAC[MLK_imp_trans; MLK_imp_swap; MLK_imp_trans_th]);;

let MLK_ex_falso_th = prove
 (`!p. [S . H |~ False --> p]`,
  MESON_TAC[MLK_imp_trans; MLK_axiom_addimp; MLK_axiom_doubleneg]);;

let MLK_ex_falso = prove
 (`!p. [S . H |~ False] ==> [S . H |~ p]`,
  MESON_TAC[MLK_ex_falso_th; MLK_modusponens]);;

let MLK_imp_contr_th = prove
 (`!p q. [S . H |~ (p --> False) --> (p --> q)]`,
  MESON_TAC[MLK_imp_add_assum; MLK_ex_falso_th]);;

let MLK_contrad = prove
 (`!p. [S . H |~ (p --> False) --> p] ==> [S . H |~ p]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_distribimp;
            MLK_imp_refl_th; MLK_axiom_doubleneg]);;

let MLK_bool_cases = prove
 (`!p q. [S . H |~ p --> q] /\ [S . H |~ (p --> False) --> q]
         ==> [S . H |~ q]`,
  MESON_TAC[MLK_contrad; MLK_imp_trans; GLimp_add_concl]);;

let MLK_imp_false_rule = prove
 (`!p q r. [S . H |~ (q --> False) --> p --> r]
           ==> [S . H |~ ((p --> q) --> False) --> r]`,
  MESON_TAC[GLimp_add_concl; MLK_imp_add_assum; MLK_ex_falso_th;
            MLK_axiom_addimp; MLK_imp_swap; MLK_imp_trans;
            MLK_axiom_doubleneg; MLK_imp_unduplicate]);;

let MLK_imp_true_rule = prove
 (`!p q r. [S . H |~ (p --> False) --> r] /\ [S . H |~ q --> r]
           ==> [S . H |~ (p --> q) --> r]`,
  MESON_TAC[MLK_imp_insert; MLK_imp_swap; MLK_modusponens;
            MLK_imp_trans_th; MLK_bool_cases]);;

let MLK_truth_th = prove
 (`[S . H |~ True]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_true; MLK_imp_refl_th; MLK_iff_imp2]);;

let MLK_and_left_th = prove
 (`!p q. [S . H |~ p && q --> p]`,
  MESON_TAC[MLK_imp_add_assum; MLK_axiom_addimp; MLK_imp_trans;
            GLimp_add_concl; MLK_axiom_doubleneg; MLK_imp_trans;
            MLK_iff_imp1; MLK_axiom_and]);;

let MLK_and_right_th = prove
 (`!p q. [S . H |~ p && q --> q]`,
  MESON_TAC[MLK_axiom_addimp; MLK_imp_trans; GLimp_add_concl;
            MLK_axiom_doubleneg; MLK_iff_imp1; MLK_axiom_and]);;

let MLK_and_pair_th = prove
 (`!p q. [S . H |~ p --> q --> p && q]`,
  MESON_TAC[MLK_iff_imp2; MLK_axiom_and; MLK_imp_swap_th; MLK_imp_add_assum;
            MLK_imp_trans2; MLK_modusponens; MLK_imp_swap; MLK_imp_refl_th]);;

let MLK_and = prove
 (`!p q. [S . H |~ p && q] <=> [S . H |~ p] /\ [S . H |~ q]`,
  MESON_TAC[MLK_and_left_th; MLK_and_right_th;
            MLK_and_pair_th; MLK_modusponens]);;

let MLK_and_elim = prove
 (`!p q r. [S . H |~ r --> p && q]
           ==> [S . H |~ r --> q] /\ [S . H |~ r --> p]`,
  MESON_TAC[MLK_and_left_th; MLK_and_right_th; MLK_imp_trans]);;

let MLK_shunt = prove
 (`!p q r. [S . H |~ p && q --> r] ==> [S . H |~ p --> q --> r]`,
  MESON_TAC[MLK_modusponens; MLK_imp_add_assum; MLK_and_pair_th]);;

let MLK_ante_conj = prove
 (`!p q r. [S . H |~ p --> q --> r] ==> [S . H |~ p && q --> r]`,
  MESON_TAC[MLK_imp_trans_chain_2; MLK_and_left_th; MLK_and_right_th]);;

let MLK_imp_imp = prove
 (`!p q r. [S . H |~ p --> q --> r] <=> [S . H |~ p && q --> r]`,
  MESON_TAC[MLK_ante_conj; MLK_shunt]);;

let MLK_modusponens_th = prove
 (`!p q. [S . H |~ (p --> q) && p --> q]`,
  MESON_TAC[MLK_imp_refl_th; MLK_ante_conj]);;

let MLK_not_not_false_th = prove
 (`!p. [S . H |~ (p --> False) --> False <-> p]`,
  MESON_TAC[MLK_imp_antisym; MLK_axiom_doubleneg;
            MLK_imp_swap; MLK_imp_refl_th]);;

let MLK_iff_sym = prove
 (`!p q. [S . H |~ p <-> q] <=> [S . H |~ q <-> p]`,
  MESON_TAC[MLK_iff_imp1; MLK_iff_imp2; MLK_imp_antisym]);;

let MLK_iff_trans = prove
 (`!p q r. [S . H |~ p <-> q] /\ [S . H |~ q <-> r]
           ==> [S . H |~ p <-> r]`,
  MESON_TAC[MLK_iff_imp1; MLK_iff_imp2; MLK_imp_trans; MLK_imp_antisym]);;

let MLK_not_not_th = prove
 (`!p. [S . H |~ Not (Not p) <-> p]`,
  MESON_TAC[MLK_iff_trans; MLK_not_not_false_th; MLK_axiom_not;
            MLK_imp_antisym; GLimp_add_concl; MLK_iff_imp1; MLK_iff_imp2]);;

let MLK_contrapos_eq = prove
 (`!p q. [S . H |~ Not p --> Not q] <=> [S . H |~ q --> p]`,
  MESON_TAC[MLK_contrapos; MLK_not_not_th; MLK_iff_imp1;
            MLK_iff_imp2; MLK_imp_trans]);;

let MLK_or_left_th = prove
 (`!p q. [S . H |~ q --> p || q]`,
  MESON_TAC[MLK_imp_trans; MLK_not_not_th; MLK_iff_imp2; MLK_and_right_th;
            MLK_contrapos; MLK_axiom_or]);;

let MLK_or_right_th = prove
 (`!p q. [S . H |~ (p --> p || q)]`,
  MESON_TAC[MLK_imp_trans; MLK_not_not_th; MLK_iff_imp2; MLK_and_left_th;
            MLK_contrapos; MLK_axiom_or]);;

let MLK_ante_disj = prove
 (`!p q r. [S . H |~ p --> r] /\ [S . H |~ q --> r]
           ==> [S . H |~ p || q --> r]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MLK_contrapos_eq] THEN
  MESON_TAC[MLK_imp_trans; MLK_imp_trans_chain_2; MLK_and_pair_th;
            MLK_contrapos_eq; MLK_not_not_th; MLK_axiom_or; MLK_iff_imp1;
            MLK_iff_imp2; MLK_imp_trans]);;

let MLK_iff_def_th = prove
 (`!p q. [S . H |~ (p <-> q) <-> (p --> q) && (q --> p)]`,
  MESON_TAC[MLK_imp_antisym; MLK_imp_trans_chain_2; MLK_axiom_iffimp1;
            MLK_axiom_iffimp2; MLK_and_pair_th; MLK_axiom_impiff;
            MLK_imp_trans_chain_2; MLK_and_left_th; MLK_and_right_th]);;

let MLK_iff_refl_th = prove
 (`!p. [S . H |~ p <-> p]`,
  MESON_TAC[MLK_imp_antisym; MLK_imp_refl_th]);;

let MLK_imp_box = prove
 (`!p q. [S . {} |~ p --> q] ==> [S . H |~ Box p --> Box q]`,
  MESON_TAC[MLK_modusponens; MLK_necessitation; MLK_axiom_boximp;
            MODPROVES_MONO2; EMPTY_SUBSET]);;

let MLK_box_moduspones = prove
 (`!p q. [S . {} |~ p --> q] /\ [S . H |~ Box p] ==> [S . H |~ Box q]`,
  MESON_TAC[MLK_imp_box; MLK_modusponens; MODPROVES_MONO2; EMPTY_SUBSET]);;

let MLK_box_and = prove
 (`!p q. [S . H |~ Box(p && q)] ==> [S . H |~ Box p && Box q]`,
 MESON_TAC[MLK_and_left_th; MLK_and_right_th; MLK_imp_box;
           MLK_box_moduspones; MLK_and]);;

let MLK_box_and_inv = prove
 (`!p q. [S . H |~ Box p && Box q] ==> [S . H |~ Box (p && q)]`,
  MESON_TAC[MLK_and_pair_th; MLK_imp_box; MLK_axiom_boximp;
            MLK_imp_trans; MLK_ante_conj; MLK_modusponens]);;

let MLK_and_comm = prove
 (`!p q . [S . H |~ p && q] <=> [S . H |~ q && p]`,
 MESON_TAC[MLK_and]);;

let MLK_and_assoc = prove
 (`!p q r. [S . H |~ (p && q) && r] <=> [S . H |~ p && (q && r)]`,
 MESON_TAC[MLK_and]);;

let MLK_disj_imp = prove
 (`!p q r. [S . H |~ p || q --> r] <=>
           [S . H |~ p --> r] /\ [S . H |~ q --> r]`,
  MESON_TAC[MLK_ante_disj; MLK_or_right_th; MLK_or_left_th; MLK_imp_trans]);;

let MLK_or_elim = prove
 (`!p q r. [S . H |~ p || q] /\ [S . H |~ p --> r] /\ [S . H |~ q --> r]
           ==> [S . H |~ r]`,
  MESON_TAC[MLK_disj_imp; MLK_modusponens]);;

let MLK_or_comm = prove
 (`!p q . [S . H |~ p || q] <=> [S . H |~ q || p]`,
  MESON_TAC[MLK_or_right_th; MLK_or_left_th; MLK_modusponens; MLK_disj_imp]);;

let MLK_or_assoc = prove
 (`!p q r. [S . H |~ (p || q) || r] <=> [S . H |~ p || (q || r)]`,
  MESON_TAC[MLK_or_right_th; MLK_or_left_th; MLK_modusponens; MLK_disj_imp]);;

let MLK_or_intror = prove
 (`!p q. [S . H |~ q] ==> [S . H |~ p || q]`,
  MESON_TAC[MLK_or_left_th; MLK_modusponens]);;

let MLK_or_introl = prove
 (`!p q. [S . H |~ p] ==> [S . H |~ (p || q)]`,
  MESON_TAC[MLK_or_right_th; MLK_modusponens]);;

let MLK_or_transl = prove
 (`!p q r. [S . H |~ p --> q] ==> [S . H |~ p --> q || r]`,
  MESON_TAC[MLK_or_right_th; MLK_imp_trans]);;

let MLK_or_transr = prove
 (`!p q r. [S . H |~ p --> r] ==> [S . H |~ p --> q || r]`,
  MESON_TAC[MLK_or_left_th; MLK_imp_trans]);;

let MLK_frege = prove
 (`!p q r.[S . H |~ p --> q --> r] /\ [S . H |~ p --> q]
          ==> [S . H |~ (p --> r)]`,
  MESON_TAC[MLK_axiom_distribimp; MLK_modusponens; MLK_shunt; MLK_ante_conj]);;

let MLK_and_intro = prove
(`!p q r. [S . H |~ p --> q] /\ [S . H |~ p --> r]
          ==> [S . H |~ (p --> q && r)]`,
 MESON_TAC[MLK_and_pair_th; MLK_imp_trans_chain_2]);;

let MLK_not_def = prove
 (`!p. [S . H |~ Not p] <=> [S . H |~ (p --> False)]`,
   MESON_TAC[MLK_axiom_not; MLK_modusponens; MLK_iff_imp1; MLK_iff_imp2]);;

let MLK_not_false = prove
 (`!S. [S . {} |~ Not False]`,
  REWRITE_TAC[MLK_not_def; MLK_imp_refl_th]);;

let MLK_NC = prove
 (`!p. [S . H |~ p  && Not p] <=> [S . H |~ False]`,
  MESON_TAC[MLK_not_def; MLK_modusponens; MLK_and; MLK_ex_falso]);;

let MLK_nc_th = prove
 (`!p. [S . H |~ p && Not p --> False]`,
  MESON_TAC[MLK_ante_conj; MLK_imp_swap; MLK_axiom_not;
            MLK_axiom_iffimp1; MLK_modusponens]);;

let MLK_imp_clauses = prove
 (`(!p. [S . H |~ p --> True]) /\
   (!p. [S . H |~ p --> False] <=> [S . H |~ Not p]) /\
   (!p. [S . H |~ True --> p] <=> [S . H |~ p]) /\
   (!p. [S . H |~ False --> p])`,
  SIMP_TAC[MLK_truth_th; MLK_add_assum; MLK_not_def; MLK_ex_falso_th] THEN
  GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[MLK_modusponens; MLK_truth_th];
   MESON_TAC[MLK_add_assum]]);;

let MLK_and_left_true_th = prove
 (`!p. [S . H |~ True && p <-> p]`,
  GEN_TAC THEN MATCH_MP_TAC MLK_imp_antisym THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC MLK_and_right_th; ALL_TAC] THEN
  MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_imp_refl_th; MLK_imp_clauses]);;

let MLK_or_and_distr = prove
 (`!p q r. [S . H |~ (p || q) && r] ==> [S . H |~ (p && r) || (q && r)]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MLK_and] THEN STRIP_TAC THEN
  MATCH_MP_TAC MLK_or_elim THEN EXISTS_TAC `p:form` THEN
  EXISTS_TAC `q :form` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_or_transl THEN MATCH_MP_TAC MLK_and_intro THEN
   REWRITE_TAC[MLK_imp_refl_th] THEN ASM_SIMP_TAC[MLK_add_assum];
   MATCH_MP_TAC MLK_or_transr THEN MATCH_MP_TAC MLK_and_intro THEN
   REWRITE_TAC[MLK_imp_refl_th] THEN ASM_SIMP_TAC[MLK_add_assum]]);;

let MLK_and_or_distr = prove
 (`!p q r. [S . H |~ (p && q) || r] ==> [S . H |~ (p || r) && (q || r)]`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MLK_and] THEN DISCH_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC MLK_or_elim THEN
  MAP_EVERY EXISTS_TAC [`p && q`; `r:form`] THEN
  ASM_REWRITE_TAC[MLK_or_left_th] THEN MATCH_MP_TAC MLK_or_transl THEN
  ASM_REWRITE_TAC[MLK_and_left_th; MLK_and_right_th]);;

let MLK_or_and_distr_inv = prove
 (`!p q r. [S . H |~ (p && r) || (q && r)] ==> [S . H |~ (p || q) && r]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MLK_or_elim THEN
  MAP_EVERY EXISTS_TAC [`p && r`; `q && r`] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (K ALL_TAC) THEN CONJ_TAC THEN MATCH_MP_TAC MLK_and_intro THEN
  CONJ_TAC THEN REWRITE_TAC[MLK_and_left_th; MLK_and_right_th] THENL
  [MATCH_MP_TAC MLK_or_transl THEN MATCH_ACCEPT_TAC MLK_and_left_th;
   MATCH_MP_TAC MLK_or_transr THEN MATCH_ACCEPT_TAC MLK_and_left_th]);;

let MLK_or_and_distr_equiv = prove
(`!p q r. [S . H |~ (p || q) && r] <=> [S . H |~ (p && r) || (q && r)]`,
 MESON_TAC[MLK_or_and_distr; MLK_or_and_distr_inv]);;

let MLK_and_or_distr_inv_prelim = prove
 (`!p q r. [S . H |~ (p || r) && (q || r)] ==> [S . H |~ q --> (p && q) || r]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLK_and] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] MLK_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_shunt THEN MATCH_ACCEPT_TAC MLK_or_right_th; ALL_TAC] THEN
  MATCH_MP_TAC MLK_imp_insert THEN MATCH_ACCEPT_TAC MLK_or_left_th);;

let MLK_and_or_distr_inv = prove
 (`!p q r. [S . H |~ (p || r) && (q || r)] ==> [S . H |~ (p && q) || r]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLK_and] THEN INTRO_TAC "pr qr" THEN
  MATCH_MP_TAC (SPECL [`p:form`; `r:form`] MLK_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "pr" (K ALL_TAC) THEN
  REWRITE_TAC[MLK_or_left_th] THEN
  MATCH_MP_TAC (SPECL [`q:form`; `r:form`] MLK_or_elim) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "qr" (K ALL_TAC) THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_imp_swap THEN MATCH_MP_TAC MLK_shunt THEN
   MATCH_ACCEPT_TAC MLK_or_right_th;
   MATCH_MP_TAC MLK_imp_insert THEN MATCH_ACCEPT_TAC MLK_or_left_th]);;

let MLK_and_or_distr_equiv = prove
 (`!p q r. [S . H |~ (p && q) || r] <=> [S . H |~ (p || r) && (q || r)]`,
  MESON_TAC[MLK_and_or_distr; MLK_and_or_distr_inv]);;

let MLK_DOUBLENEG_CL = prove
 (`!p. [S . H |~ Not(Not p)] ==> [S . H |~ p]`,
 MESON_TAC[MLK_not_not_th; MLK_modusponens; MLK_iff_imp1; MLK_iff_imp2]);;

let MLK_DOUBLENEG = prove
 (`!p. [S . H |~ p] ==> [S . H |~ Not(Not p)]`,
  MESON_TAC[MLK_not_not_th; MLK_modusponens; MLK_iff_imp1; MLK_iff_imp2]);;

let MLK_and_eq_or = prove
 (`!p q. [S . H |~ p || q ]<=> [S . H |~ Not(Not p && Not q)]`,
  MESON_TAC[MLK_modusponens; MLK_axiom_or; MLK_iff_imp1; MLK_iff_imp2]);;

let MLK_tnd_th = prove
 (`!p. [S . H |~ p || Not p]`,
  GEN_TAC THEN REWRITE_TAC[MLK_and_eq_or] THEN
  REWRITE_TAC[MLK_not_def] THEN MESON_TAC[MLK_nc_th]);;

let MLK_iff_mp = prove
 (`!p q. [S . H |~ p <-> q] /\ [S . H |~ p] ==> [S . H |~ q]`,
  MESON_TAC[MLK_iff_imp1; MLK_modusponens]);;

let MLK_and_subst = prove
 (`!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
               ==> ([S . H |~ p && q] <=> [S . H |~ p' && q'])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLK_and] THEN
  ASM_MESON_TAC[MLK_iff_mp; MLK_iff_sym]);;

let MLK_imp_mono_th = prove
 (`!p p' q q'. [S . H |~ (p' --> p) && (q --> q')
                         --> (p --> q) --> (p' --> q')]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_ante_conj THEN
  MATCH_ACCEPT_TAC MLK_imp_mono_th);;

let MLK_imp_mono = prove
 (`!p p' q q'. [S . H |~ p' --> p] /\ [S . H |~ q --> q']
               ==> [S . H |~ (p --> q) --> (p' --> q')]`,
  REWRITE_TAC[GSYM MLK_and] THEN MESON_TAC[MLK_modusponens; MLK_imp_mono_th]);;

let MLK_iff = prove
 (`!p q. [S . H |~ p <-> q] ==> ([S . H |~ p] <=> [S . H |~ q])`,
  MESON_TAC[MLK_iff_imp1; MLK_iff_imp2; MLK_modusponens]);;

let MLK_iff_def = prove
 (`!p q. [S . H |~ p <-> q] <=> [S . H |~ p --> q] /\ [S . H |~ q --> p]`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[MLK_iff_imp1; MLK_iff_imp2];
   MATCH_ACCEPT_TAC MLK_imp_antisym]);;

let MLK_not_subst = prove
 (`!p q. [S . H |~ p <-> q] ==> [S . H |~ Not p <-> Not q]`,
  MESON_TAC[MLK_iff_def; MLK_iff_imp2; MLK_contrapos]);;

let MLK_not_subst_th = prove
 (`!p q. [S . H |~ p <-> q] /\ [S . H |~ Not p]  ==> [S . H |~ Not q]`,
  REPEAT STRIP_TAC THEN
   CLAIM_TAC "not_eq" `[S . H |~ Not p <-> Not q]` THENL [MATCH_MP_TAC MLK_not_subst; ALL_TAC] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_MESON_TAC [MLK_iff_mp]);;

let MLK_and_rigth_true_th = prove
 (`!p. [S . H |~ p && True <-> p]`,
  GEN_TAC THEN REWRITE_TAC[MLK_iff_def] THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC MLK_and_left_th; ALL_TAC] THEN
  MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_imp_refl_th] THEN
  MATCH_MP_TAC MLK_add_assum THEN
  MATCH_ACCEPT_TAC MLK_truth_th);;

let MLK_and_comm_th = prove
 (`!p q. [S . H |~ p && q <-> q && p]`,
  SUBGOAL_THEN `!p q. [S . H |~ p && q --> q && p]`
    (fun th -> MESON_TAC[th; MLK_iff_def]) THEN
  MESON_TAC[MLK_and_intro; MLK_and_left_th; MLK_and_right_th]);;

let MLK_and_assoc_th = prove
 (`!p q r. [S . H |~ (p && q) && r <-> p && (q && r)]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_imp_antisym THEN CONJ_TAC THEN
  MATCH_MP_TAC MLK_and_intro THEN
  MESON_TAC[MLK_and_left_th; MLK_and_right_th; MLK_imp_trans; MLK_and_intro]);;

let MLK_and_subst_th = prove
 (`!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
               ==> [S . H |~ p && q <-> p' && q']`,
  SUBGOAL_THEN
    `!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
                 ==> [S . H |~ p && q --> p' && q']`
    (fun th -> MESON_TAC[th; MLK_iff_def]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `p:form` THEN
   REWRITE_TAC[MLK_and_left_th] THEN ASM_SIMP_TAC[MLK_iff_imp1];
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `q:form` THEN
   REWRITE_TAC[MLK_and_right_th] THEN ASM_SIMP_TAC[MLK_iff_imp1]]);;

let MLK_imp_subst = prove
 (`!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
               ==> [S . H |~ (p --> q) <-> (p' --> q')]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MLK_iff_def] THEN
  POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
  SUBGOAL_THEN `!p q p' q'.
                  [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
                  ==> [S . H |~ (p --> q) --> (p' --> q')]`
    (fun th -> MESON_TAC[th; MLK_iff_sym]) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MLK_imp_mono THEN
  ASM_MESON_TAC[MLK_iff_imp1; MLK_iff_sym]);;

let MLK_de_morgan_and_th = prove
 (`!p q. [S . H |~ Not (p && q) <-> Not p || Not q]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `Not (Not (Not p) && Not (Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_not_subst THEN ONCE_REWRITE_TAC[MLK_iff_sym] THEN
   MATCH_MP_TAC MLK_and_subst_th THEN CONJ_TAC THEN
   MATCH_ACCEPT_TAC MLK_not_not_th;
   ONCE_REWRITE_TAC[MLK_iff_sym] THEN MATCH_ACCEPT_TAC MLK_axiom_or]);;

let MLK_iff_sym_th = prove
 (`!p q. [S . H |~ (p <-> q) <-> (q <-> p)]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN ASM_REWRITE_TAC[MLK_iff_def_th] THEN
  ONCE_REWRITE_TAC[MLK_iff_sym] THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `(q --> p) && (p --> q)` THEN
  REWRITE_TAC[MLK_iff_def_th; MLK_and_comm_th]);;

let MLK_iff_true_th = prove
 (`(!p. [S . H |~ (p <-> True) <-> p]) /\
   (!p. [S . H |~ (True <-> p) <-> p])`,
  CLAIM_TAC "1" `!p. [S . H |~ (p <-> True) <-> p]` THENL
  [GEN_TAC THEN MATCH_MP_TAC MLK_imp_antisym THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `True --> p` THEN CONJ_TAC THENL
    [MATCH_ACCEPT_TAC MLK_axiom_iffimp2; ALL_TAC] THEN
    MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(True --> p) && True` THEN
    REWRITE_TAC[MLK_modusponens_th] THEN MATCH_MP_TAC MLK_and_intro THEN
    REWRITE_TAC[MLK_imp_refl_th] THEN MATCH_MP_TAC MLK_add_assum THEN
    MATCH_ACCEPT_TAC MLK_truth_th;
    ALL_TAC] THEN
   MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `(p --> True) && (True --> p)` THEN
   CONJ_TAC THENL [ALL_TAC; MESON_TAC[MLK_iff_def_th; MLK_iff_imp2]] THEN
   MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_axiom_addimp] THEN
   SIMP_TAC[MLK_add_assum; MLK_truth_th];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `p <-> True` THEN ASM_REWRITE_TAC[MLK_iff_sym_th]);;

let MLK_or_subst_th = prove
 (`!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
               ==> [S . H |~ p || q <-> p' || q']`,
  SUBGOAL_THEN
    `!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
                 ==> [S . H |~ p || q --> p' || q']`
    (fun th -> MESON_TAC[th; MLK_iff_sym; MLK_iff_def]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLK_disj_imp] THEN CONJ_TAC THEN
  MATCH_MP_TAC MLK_frege THENL
  [EXISTS_TAC `p':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLK_add_assum THEN MATCH_ACCEPT_TAC MLK_or_right_th;
    ASM_SIMP_TAC[MLK_iff_imp1]];
   EXISTS_TAC `q':form` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLK_add_assum THEN MATCH_ACCEPT_TAC MLK_or_left_th;
    ASM_SIMP_TAC[MLK_iff_imp1]]]);;

let MLK_or_subst_right = prove
 (`!p q1 q2. [S . H |~ q1 <-> q2] ==> [S . H |~ p || q1 <-> p || q2]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_or_subst_th THEN
  ASM_REWRITE_TAC[MLK_iff_refl_th]);;

let MLK_or_rid_th = prove
 (`!p. [S . H |~ p || False <-> p]`,
  GEN_TAC THEN REWRITE_TAC[MLK_iff_def] THEN CONJ_TAC THENL
  [REWRITE_TAC[MLK_disj_imp; MLK_imp_refl_th; MLK_ex_falso_th];
   MATCH_ACCEPT_TAC MLK_or_right_th]);;

let MLK_or_lid_th = prove
 (`!p. [S . H |~ False || p <-> p]`,
  GEN_TAC THEN REWRITE_TAC[MLK_iff_def] THEN CONJ_TAC THENL
  [REWRITE_TAC[MLK_disj_imp; MLK_imp_refl_th; MLK_ex_falso_th];
   MATCH_ACCEPT_TAC MLK_or_left_th]);;

let MLK_or_assoc_left_th = prove
 (`!p q r. [S . H |~ p || (q || r) --> (p || q) || r]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLK_disj_imp] THEN
  MESON_TAC[MLK_or_left_th; MLK_or_right_th; MLK_imp_trans]);;

let MLK_or_assoc_right_th = prove
 (`!p q r. [S . H |~ (p || q) || r --> p || (q || r)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLK_disj_imp] THEN
  MESON_TAC[MLK_or_left_th; MLK_or_right_th; MLK_imp_trans]);;

let MLK_or_assoc_th = prove
 (`!p q r. [S . H |~ p || (q || r) <-> (p || q) || r]`,
  REWRITE_TAC[MLK_iff_def; MLK_or_assoc_left_th; MLK_or_assoc_right_th]);;

let MLK_and_or_ldistrib_th = prove
 (`!p q r. [S . H |~ p && (q || r) <-> p && q || p && r]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLK_iff_def; MLK_disj_imp] THEN
  REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC MLK_and_intro) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MLK_ante_conj THENL
  [MATCH_MP_TAC MLK_imp_swap THEN REWRITE_TAC[MLK_disj_imp] THEN
  CONJ_TAC THEN MATCH_MP_TAC MLK_imp_swap THEN MATCH_MP_TAC MLK_shunt THENL
   [MATCH_ACCEPT_TAC MLK_or_right_th; MATCH_ACCEPT_TAC MLK_or_left_th];
   MATCH_ACCEPT_TAC MLK_axiom_addimp;
   MATCH_MP_TAC MLK_add_assum THEN MATCH_ACCEPT_TAC MLK_or_right_th;
   MATCH_ACCEPT_TAC MLK_axiom_addimp;
   MATCH_MP_TAC MLK_add_assum THEN MATCH_ACCEPT_TAC MLK_or_left_th]);;

let MLK_not_true_th = prove
 (`[S . H |~ Not True <-> False]`,
  REWRITE_TAC[MLK_iff_def; MLK_ex_falso_th; GSYM MLK_not_def] THEN
  MATCH_MP_TAC MLK_iff_mp THEN EXISTS_TAC `True` THEN
  REWRITE_TAC[MLK_truth_th] THEN ONCE_REWRITE_TAC[MLK_iff_sym] THEN
  MATCH_ACCEPT_TAC MLK_not_not_th);;

let MLK_and_subst_right_th = prove
 (`!p q1 q2. [S . H |~ (q1 <-> q2) --> (p && q1 <-> p && q2)]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `(p && q1 --> p && q2) && (p && q2 --> p && q1)` THEN
  CONJ_TAC THENL
  [ALL_TAC;
   MATCH_MP_TAC MLK_iff_imp2 THEN MATCH_ACCEPT_TAC MLK_iff_def_th] THEN
  SUBGOAL_THEN `!p q1 q2. [S . H |~ (q1 <-> q2) --> (p && q1 --> p && q2)]`
    (fun th -> MATCH_MP_TAC MLK_and_intro THEN
      MESON_TAC[th; MLK_and_comm_th; MLK_imp_trans; MLK_iff_def_th;
                MLK_iff_imp1; MLK_iff_imp2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_shunt THEN
  MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
  [MESON_TAC[MLK_and_left_th; MLK_and_right_th; MLK_imp_trans]; ALL_TAC] THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(q1 <-> q2) && q1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_and_left_th] THEN
   MESON_TAC[MLK_and_right_th; MLK_imp_trans];
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(q1 --> q2) && q1` THEN
   REWRITE_TAC[MLK_modusponens_th] THEN MATCH_MP_TAC MLK_and_intro THEN
   REWRITE_TAC[MLK_and_right_th] THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `(q1 <-> q2)` THEN REWRITE_TAC[MLK_and_left_th] THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN
   REWRITE_TAC[MLK_and_left_th] THEN MATCH_MP_TAC MLK_iff_imp1 THEN
   MATCH_ACCEPT_TAC MLK_iff_def_th]);;

let MLK_and_subst_left_th = prove
 (`!p1 p2 q. [S . H |~ (p1 <-> p2) --> (p1 && q <-> p2 && q)]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `(p1 && q --> p2 && q) && (p2 && q --> p1 && q)` THEN
  CONJ_TAC THENL
  [ALL_TAC;
   MATCH_MP_TAC MLK_iff_imp2 THEN MATCH_ACCEPT_TAC MLK_iff_def_th] THEN
  SUBGOAL_THEN `!p1 p2 q. [S . H |~ (p1 <-> p2) --> (p1 && q --> p2 && q)]`
    (fun th -> MATCH_MP_TAC MLK_and_intro THEN
      MESON_TAC[th; MLK_and_comm_th; MLK_imp_trans; MLK_iff_def_th;
                MLK_iff_imp1; MLK_iff_imp2]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_shunt THEN
  MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[MLK_and_left_th; MLK_and_right_th; MLK_imp_trans]] THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(p1 <-> p2) && p1` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MLK_and_intro THEN REWRITE_TAC[MLK_and_left_th] THEN
   MESON_TAC[MLK_and_right_th; MLK_and_left_th; MLK_imp_trans];
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(p1 --> p2) && p1` THEN
   REWRITE_TAC[MLK_modusponens_th] THEN MATCH_MP_TAC MLK_and_intro THEN
   REWRITE_TAC[MLK_and_right_th] THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `(p1 <-> p2)` THEN REWRITE_TAC[MLK_and_left_th] THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(p1 --> p2) && (p2 --> p1)` THEN
   REWRITE_TAC[MLK_and_left_th] THEN MATCH_MP_TAC MLK_iff_imp1 THEN
   MATCH_ACCEPT_TAC MLK_iff_def_th]);;

let MLK_contrapos_th = prove
 (`!p q. [S . H |~ (p --> q) --> (Not q --> Not p)]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_imp_swap THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(q --> False)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC MLK_iff_imp1 THEN MATCH_ACCEPT_TAC MLK_axiom_not;
   MATCH_MP_TAC MLK_shunt THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `p --> False` THEN CONJ_TAC THENL
   [MESON_TAC[MLK_ante_conj; MLK_imp_trans_th];
    MESON_TAC[MLK_axiom_not; MLK_iff_imp2]]]);;

let MLK_contrapos_eq_th = prove
 (`!p q. [S . H |~ (p --> q) <-> (Not q --> Not p)]`,
  SUBGOAL_THEN `!p q. [S . H |~ (Not q --> Not p) --> (p --> q)]`
    (fun th -> MESON_TAC[th; MLK_iff_def; MLK_contrapos_th]) THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `Not (Not p) --> Not (Not q)` THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC MLK_contrapos_th; ALL_TAC] THEN
  MATCH_MP_TAC MLK_iff_imp1 THEN MATCH_MP_TAC MLK_imp_subst THEN
  MESON_TAC[MLK_not_not_th]);;

let MLK_iff_sym_th = prove
 (`!p q. [S . H |~ (p <-> q) --> (q <-> p)]`,
  REPEAT  GEN_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN CONJ_TAC THENL
  [MESON_TAC[MLK_iff_def_th; MLK_iff_imp1]; ALL_TAC] THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(q --> p) && (p --> q)` THEN
  CONJ_TAC THENL
  [MESON_TAC[MLK_and_comm_th; MLK_iff_imp1];
   MESON_TAC[MLK_iff_def_th; MLK_iff_imp2]]);;

let MLK_de_morgan_or_th = prove
 (`!p q. [S . H |~ Not (p || q) <-> Not p && Not q]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `Not (Not (Not p && Not q))` THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_not_subst THEN MATCH_ACCEPT_TAC MLK_axiom_or;
  MATCH_ACCEPT_TAC MLK_not_not_th]);;

let MLK_crysippus_th = prove
 (`!p q. [S . H |~ Not (p --> q) <-> p && Not q]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_iff_trans THEN
  EXISTS_TAC `(p --> Not q --> False) --> False` THEN CONJ_TAC THENL
  [ALL_TAC; MESON_TAC[MLK_axiom_and; MLK_iff_sym]] THEN
  MATCH_MP_TAC MLK_iff_trans THEN EXISTS_TAC `Not (p --> Not q --> False)` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_ACCEPT_TAC MLK_axiom_not] THEN
  MATCH_MP_TAC MLK_not_subst THEN
  MATCH_MP_TAC MLK_imp_subst THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC MLK_iff_refl_th; ALL_TAC] THEN
  MATCH_MP_TAC MLK_iff_trans THEN EXISTS_TAC `Not (Not q)` THEN CONJ_TAC THENL
  [MESON_TAC[MLK_not_not_th; MLK_iff_sym]; MATCH_ACCEPT_TAC MLK_axiom_not]);;

(* ------------------------------------------------------------------------- *)
(* Substitution.                                                             *)
(* ------------------------------------------------------------------------- *)

let SUBST = new_recursive_definition form_RECURSION
  `(!f. SUBST f True = True) /\
   (!f. SUBST f False = False) /\
   (!f a. SUBST f (Atom a) = f a) /\
   (!f p. SUBST f (Not p) = Not (SUBST f p)) /\
   (!f p q. SUBST f (p && q) = SUBST f p && SUBST f q) /\
   (!f p q. SUBST f (p || q) = SUBST f p || SUBST f q) /\
   (!f p q. SUBST f (p --> q) = SUBST f p --> SUBST f q) /\
   (!f p q. SUBST f (p <-> q) = SUBST f p <-> SUBST f q) /\
   (!f p. SUBST f (Box p) = Box (SUBST f p))`;;

let KAXIOM_SUBST = prove
 (`!f p. KAXIOM p ==> KAXIOM (SUBST f p)`,
  GEN_TAC THEN MATCH_MP_TAC KAXIOM_INDUCT THEN
  REWRITE_TAC[SUBST; KAXIOM_RULES]);;

let SUBST_IMP = prove
 (`!S f H p. (!q. q IN S ==> SUBST f q IN S) /\ [S . H |~ p]
             ==> [S . IMAGE (SUBST f) H |~ SUBST f p]`,
  FIX_TAC "S f" THEN C SUBGOAL_THEN (fun th -> MESON_TAC[th])
   `(!q. q IN S ==> SUBST f q IN S)
    ==> !H p. [S . H |~ p] ==> [S . IMAGE (SUBST f) H |~ SUBST f p]` THEN
  INTRO_TAC "S" THEN MATCH_MP_TAC MODPROVES_INDUCT THEN
  CONJ_TAC THENL [MESON_TAC[MODPROVES_RULES; KAXIOM_SUBST]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MODPROVES_RULES]; ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `SUBST f p IN IMAGE (SUBST f) H`
    (fun th -> MESON_TAC[th; MODPROVES_RULES]) THEN
   ASM SET_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBST] THEN MESON_TAC[MODPROVES_RULES]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; SUBST] THEN MESON_TAC[MODPROVES_RULES]);;

let SUBSTITUTION_LEMMA = prove
 (`!S f H p q.
     (!q. q IN S ==> SUBST f q IN S) /\ [S . H |~ p <-> q]
     ==> [S . IMAGE (SUBST f) H |~ SUBST f p <-> SUBST f q]`,
  REWRITE_TAC[GSYM SUBST; SUBST_IMP]);;

(* ------------------------------------------------------------------------- *)
(* SUBST_IFF.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLK_iff_subst = prove
 (`!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
               ==> [S . H |~ (p <-> q) <-> (p' <-> q')]`,
  SUBGOAL_THEN `!p q p' q'.
                [S . H |~ p <-> p'] /\ [S . H |~ q <-> q']
                ==> [S . H |~ (p <-> q) --> (p' <-> q')]`
    (fun th -> REPEAT STRIP_TAC THEN REWRITE_TAC[MLK_iff_def] THEN
                ASM_MESON_TAC[th; MLK_iff_sym]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `(p --> q) && (q --> p)` THEN
  CONJ_TAC THENL [MESON_TAC[MLK_iff_def_th; MLK_iff_imp1]; ALL_TAC] THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `(p' --> q') && (q' --> p')` THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[MLK_iff_def_th; MLK_iff_imp2]] THEN
  MATCH_MP_TAC MLK_and_intro THEN
  CONJ_TAC THEN MATCH_MP_TAC MLK_ante_conj THENL
  [MATCH_MP_TAC MLK_imp_insert THEN MATCH_MP_TAC MLK_imp_swap THEN
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `p:form` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[MLK_iff_imp2]; ALL_TAC] THEN
   MATCH_MP_TAC MLK_shunt THEN MATCH_MP_TAC MLK_imp_trans THEN
   EXISTS_TAC `q:form` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[MLK_iff_imp1]] THEN
   MATCH_MP_TAC MLK_ante_conj THEN MATCH_MP_TAC MLK_imp_swap THEN
   MATCH_ACCEPT_TAC MLK_imp_refl_th;
   ALL_TAC] THEN
  MATCH_MP_TAC MLK_add_assum THEN MATCH_MP_TAC MLK_imp_swap THEN
  MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `q:form` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MLK_iff_imp2]; ALL_TAC] THEN
  MATCH_MP_TAC MLK_imp_swap THEN MATCH_MP_TAC MLK_imp_add_assum THEN
  ASM_MESON_TAC[MLK_iff_imp1]);;

let MLK_iff_mp_subst= prove
(`!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q'] /\
                [S . H |~ p <-> q] ==> [S . H |~ p' <-> q']`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_iff_mp THEN
  EXISTS_TAC `p <-> q` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MLK_iff_subst; MLK_imp_subst]);;

let MLK_imp_mp_subst = prove
 (`!p p' q q'. [S . H |~ p <-> p'] /\ [S . H |~ q <-> q'] /\
                [S . H |~ p --> q] ==> [S . H |~ p' --> q']`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_iff_mp THEN
  EXISTS_TAC `p --> q` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MLK_iff_subst; MLK_imp_subst]);;

let MLK_box_iff_th = prove
 (`!p q. [S . H |~ Box (p <-> q) --> (Box p <-> Box q)]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLK_imp_trans THEN
  EXISTS_TAC `(Box p --> Box q) && (Box q --> Box p)` THEN CONJ_TAC THENL
  [ALL_TAC; MATCH_MP_TAC MLK_iff_imp2 THEN
  MATCH_ACCEPT_TAC MLK_iff_def_th] THEN
  MATCH_MP_TAC MLK_and_intro THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Box (p --> q)` THEN
   REWRITE_TAC[MLK_axiom_boximp] THEN MATCH_MP_TAC MLK_imp_box THEN
   MATCH_ACCEPT_TAC MLK_axiom_iffimp1;
   MATCH_MP_TAC MLK_imp_trans THEN EXISTS_TAC `Box (q --> p)` THEN
   REWRITE_TAC[MLK_axiom_boximp] THEN MATCH_MP_TAC MLK_imp_box THEN
   MATCH_ACCEPT_TAC MLK_axiom_iffimp2]);;

let MLK_box_iff = prove
 (`!p q. [S . H |~ Box (p <-> q)] ==> [S . H |~ Box p <-> Box q]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLK_imp_antisym THEN CONJ_TAC THENL
  [MATCH_MP_TAC MLK_modusponens THEN EXISTS_TAC `Box (p --> q)` THEN
   REWRITE_TAC[MLK_axiom_boximp] THEN
   MATCH_MP_TAC MLK_box_moduspones THEN EXISTS_TAC `(p <-> q)` THEN
   ASM_REWRITE_TAC[MLK_axiom_iffimp1];
   MATCH_MP_TAC MLK_modusponens THEN EXISTS_TAC `Box (q --> p)` THEN
   REWRITE_TAC[MLK_axiom_boximp] THEN
   MATCH_MP_TAC MLK_box_moduspones THEN EXISTS_TAC `(p <-> q)` THEN
   ASM_REWRITE_TAC[MLK_axiom_iffimp2]]);;

let MLK_box_subst = prove
 (`!p q. [S . {} |~ p <-> q] ==> [S . H |~ Box p <-> Box q]`,
  MESON_TAC[MLK_box_iff; MLK_necessitation; MODPROVES_MONO2; EMPTY_SUBSET]);;

let SUBST_IFF = prove
 (`!S H f g p. (!a. [S . {} |~ f a <-> g a])
               ==> [S . H |~ SUBST f p <-> SUBST g p]`,
  FIX_TAC "S f g" THEN
  C SUBGOAL_THEN (fun th -> MESON_TAC[th])
    `(!a. [S . {} |~ f a <-> g a])
     ==> !p H. [S . H |~ SUBST f p <-> SUBST g p]` THEN
  INTRO_TAC "fg" THEN MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC[SUBST] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLK_iff_refl_th] THEN
  REWRITE_TAC[SUBST; MLK_iff_refl_th] THEN REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC MODPROVES_MONO2 THEN ASM_MESON_TAC[EMPTY_SUBSET];
   MATCH_MP_TAC MLK_not_subst THEN POP_ASSUM MATCH_ACCEPT_TAC;
   MATCH_MP_TAC MLK_and_subst_th THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC MLK_or_subst_th THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC MLK_imp_subst THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC MLK_iff_subst THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC MLK_box_subst THEN POP_ASSUM MATCH_ACCEPT_TAC]);;

(* ----------------------------------------------------------------------- *)
(* Some modal propositional schemas and derived rules.                     *)
(* ----------------------------------------------------------------------- *)

let MLK_box_and_th = prove
 (`!p q. [S . H |~ Box(p && q) --> (Box p && Box q)]`,
  MESON_TAC[MLK_and_intro; MLK_imp_box;MLK_and_left_th;MLK_and_right_th]);;

let MLK_box_and_inv_th = prove
 (`!p q. [S . H |~ (Box p && Box q) --> Box (p && q)]`,
  MESON_TAC[MLK_ante_conj; MLK_imp_trans; MLK_imp_box; MLK_and_pair_th;
            MLK_axiom_boximp; MLK_shunt]);;

(* ------------------------------------------------------------------------- *)
(* Deduction lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let MODPROVES_DEDUCTION_LEMMA_INSERT = prove
 (`!S H p q. [S . H |~ p --> q] ==> [S . p INSERT H |~ q]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CLAIM_TAC "rmk1" `[S . p INSERT H |~ p]` THENL
  [MESON_TAC[MODPROVES_RULES; IN_INSERT]; ALL_TAC] THEN
  CLAIM_TAC "rmk2" `[S . p INSERT H |~ p --> q]` THENL
  [ASM_MESON_TAC[MODPROVES_MONO2; SET_RULE `s SUBSET p:form INSERT s`];
   ALL_TAC] THEN
  HYP MESON_TAC "rmk1 rmk2" [MODPROVES_RULES]);;

let MODPROVES_DEDUCTION_LEMMA_DELETE = prove
 (`!S H p q. [S . H |~ q] /\ p IN H ==> [S . H DELETE p |~ p --> q]`,
  FIX_TAC "S p" THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC MODPROVES_INDUCT_STRONG THEN
  CONJ_TAC THENL [MESON_TAC[MLK_add_assum; MODPROVES_RULES]; ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[MODPROVES_RULES; MLK_add_assum]; ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "!H [q]; q; p" THEN
   ASM_CASES_TAC `p:form = q` THENL
   [ASM_MESON_TAC[MLK_imp_refl_th]; ALL_TAC] THEN
   CLAIM_TAC "rmk" `q:form IN H DELETE p` THENL [ASM SET_TAC []; ALL_TAC] THEN
   ASM_MESON_TAC[MODPROVES_RULES; MLK_add_assum];
   ALL_TAC] THEN
   CONJ_TAC THENL
   [MESON_TAC[MODPROVES_RULES; MLK_axiom_distribimp]; ALL_TAC] THEN
   MESON_TAC[MODPROVES_RULES; MLK_add_assum]);;

let MODPROVES_DEDUCTION_LEMMA = prove
 (`!S H p q. [S . H |~ p --> q] <=> [S . p INSERT H |~ q]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `[S . p INSERT H |~ q] ==> [S . H |~ p --> q]`
    (fun th -> MESON_TAC[th; MODPROVES_DEDUCTION_LEMMA_INSERT]) THEN
  ASM_CASES_TAC `p:form IN H` THENL
  [SUBGOAL_THEN `p:form INSERT H = H` SUBST1_TAC THENL
   [ASM SET_TAC []; ALL_TAC] THEN
   MESON_TAC[MODPROVES_RULES; MLK_add_assum]; ALL_TAC] THEN
  INTRO_TAC "hp" THEN
  SUBGOAL_THEN `H = (p:form INSERT H) DELETE p` SUBST1_TAC THENL
  [ASM SET_TAC []; ALL_TAC] THEN
  MATCH_MP_TAC MODPROVES_DEDUCTION_LEMMA_DELETE THEN
  ASM_REWRITE_TAC[IN_INSERT]);;
