(* ========================================================================= *)
(* Esperimento: Cambiare atomi con metavariabili e viceversa usando SUBST.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let SUBST_IMP_ALT = prove
 (`!S H p. [S . H |~ p]
           ==> !f. (!q. q IN S ==> SUBST f q IN S)
                   ==> [S . IMAGE (SUBST f) H |~ SUBST f p]`,
  MESON_TAC[SUBST_IMP]);;

let FORALL_IN_GL_AX = prove
 (`!P. (!p. p IN GL_AX ==> P p) <=> (!p. P (LOB_SCHEMA p))`,
  REWRITE_TAC[GL_AX; FORALL_IN_GSPEC; IN_UNIV]);;

let SUBST_LOB_SCHEMA = prove
 (`!f p. SUBST f (LOB_SCHEMA p) = LOB_SCHEMA (SUBST f p)`,
  REWRITE_TAC[SUBST; LOB_SCHEMA_DEF]);;

let GL_SCHEMATIC = prove
 (`!p. p IN GL_AX ==> SUBST f p IN GL_AX`,
  REWRITE_TAC[FORALL_IN_GL_AX; SUBST_LOB_SCHEMA] THEN
  REWRITE_TAC[GL_AX] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Esempio: p --> q                                                          *)
(* ------------------------------------------------------------------------- *)

g `[GL_AX . {} |~ Atom "p" --> Atom "q"] <=>
   (!p q. [GL_AX . {} |~ p --> q])`;;
e (SUBGOAL_THEN
    `[GL_AX . {} |~ Atom "p" --> Atom "q"]
     ==> (!p q. [GL_AX . {} |~ p --> q])`
    (fun th -> MESON_TAC[th]));;
e (INTRO_TAC "hp; !p q");;
e (POP_ASSUM (MP_TAC o MATCH_MP SUBST_IMP_ALT));;
e (REWRITE_TAC[IMAGE_CLAUSES; GL_SCHEMATIC]);;
e (DISCH_THEN (MP_TAC o SPEC `\s. if s = "p" then p else q:form`));;
e (REWRITE_TAC[SUBST; CONS_11; injectivity "char"]);;
top_thm();;

let tm = `[GL_AX . {} |~ Atom "p" --> Atom "q"]`;;
let atoms = find_terms is_modal_atom tm;;
let ctx = map (fun a -> a,genvar `:form`) atoms;;
let swap(x,y) = y,x;;
subst (map swap ctx) tm;;
