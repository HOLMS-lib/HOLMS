# HOLMS: A HOL Light Library for Modal Systems

(c) Copyright, Antonella Bilotta, Marco Maggesi, Cosimo Perini Brogi, Leonardo Quartini 2024. <br>
(c) Copyright, Antonella Bilotta, Marco Maggesi, Cosimo Perini Brogi 2025.

See the [website](https://holms-lib.github.io/) for a brief overview of our [HOLMS library](https://github.com/HOLMS-lib/HOLMS) for the [HOL Light](https://hol-light.github.io/) theorem prover.

This repository presents a second version of HOLMS (HOL-Light Library for Modal Systems), a modular framework designed for implementing modal reasoning within the HOL Light proof assistant.  

Extending our [previous work on Gödel-Löb logic (GL)](https://doi.org/10.1007/s10817-023-09677-z), we generalize our approach to formalize modal adequacy proofs for axiomatic calculi, thereby enabling the coverage of a broader range of normal modal systems. If the first version of HOLMS, [presented at Overlay 2024](https://ceur-ws.org/Vol-3904/paper5.pdf), partially parametrized the completeness proof for GL and added the minimal system K, this second version of HOLMS fully generalizes our approach and, as a demonstration of the flexibility of our methodology, four modal system and their adequacy proofs are now implemented in HOLMS:
- **K**: the minimal system is developed in `k_completeness.ml`;
- **K4**: a system properly extended by GL is developed in `k4_completeness.ml`;
- **GL**: provability logic is developed and fully parametrized in `gl_completeness.ml`;
- **T**: a system that is not extended by GL or K4, nor is an extension of GL or K4 is developed in `t_completeness.ml`.

HOLMS lays the foundation for a comprehensive tool for modal reasoning in HOL, offering a high level of confidence and full automation by providing the essential mathematical components of principled decision algorithms for modal systems. The automated theorem prover and countermodel constructor for K and GL, already integrated into our library in `k_decid.ml` and `gl_decid.ml`, serve as evidence of the feasibility of this approach merging general purpose proof assistants, enriched sequent calculi, and formalised mathematics.

The top-level file is `make.ml`.

## Main Theorems

For each normal system S, implemented in HOLMS in its file `S_completeness.ml`, we prove the following main theorems:
1. **The Correspondence theorem for S** <br> proves that a certain set of finite frames C, distinguished by a certain accessibility relation, correspond to S (for each frame in the set if p follows from S, then p is valid in such a frame). <br>
$C= CORR S$ and equivalently $\forall F \in C (S \vdash p \implies F \vDash p) \land \forall F((S \vdash p \implies F \vDash p) \implies F \in C)$ 
(`APPRS_CORR_S`)
2. **Soundness of S with respect to CORR S**  <br>
proves that if something is a theorem of S then it is valid in its correspondent frame. <br>
$\forall p (S \vdash p \implies CORR S \vDash p)$
(`S_APPRS_VALID`)
3. **Consistency of S** <br>
proves that S cannot prove the false. <br>
$S \not \vdash \bot$
(`S_CONSISTENT`)
5. **Completeness of S related to CORR S** <br>
proves that if someting holds in the set correspondent to S, then it is a theorem of S. <br>
$\forall p (CORR S \vDash p \implies S \vdash p)$
(`S_COMPLETENESS_THM`)

For example, in `t_completeness.ml` we prove: (1) `RF_CORR_T`; (2) `T_RF_VALID`; (3) `T_CONSISTENT`; (4) `T_COMPLETENESS_THM`; (5) `T_RULE`.

Moreover, for each of this systems, HOLMS presents a **simple decision procedure** to prove whether something is a theorem of S or not (`S_RULE`) and a fully automated theorem prover and countermodel constructor for K (`k_completeness.ml`) and GL (`gl_completeness.ml`).


To generalize and parametrize the proofs of completeness for normal systems as much as possible, we develop four main theorems in `gen_completeness.ml`:
1. `GEN_TRUTH_LEMMA`;
2. `GEN_ACCESSIBILITY_LEMMA`;
3.  `GEN_COUNTERMODEL_ALT `
4.  `GEN_LEMMA_FOR_GEN_COMPLETENESS`
   

# Usage guide and source code

## Calcus Definition
```
let MODPROVES_RULES,MODPROVES_INDUCT,MODPROVES_CASES =
  new_inductive_definition
  `(!H p. KAXIOM p ==> [S . H |~ p]) /\
   (!H p. p IN S ==> [S . H |~ p]) /\
   (!H p. p IN H ==> [S . H |~ p]) /\
   (!H p q. [S . H |~ p --> q] /\ [S . H |~ p] ==> [S . H |~ q]) /\
   (!H p. [S . {} |~ p] ==> [S . H |~ Box p])`;;
```

## Deduction Lemma
```
MODPROVES_DEDUCTION_LEMMA
|- !S H p q. [S . H |~ p --> q] <=> [S . p INSERT H |~ q]
```

## Relational semantics
Kripke's Semantics of formulae.

We define, by induction on the complexity of a formula, that a certain formula $A$ **holds in a certain world $w$ of a certain model $\langle W, R, V\rangle$**. <br>
$\langle W, R, V\rangle, w \vDash A$
```
let holds =
  let pth = prove
    (`(!WP. P WP) <=> (!W:W->bool R:W->W->bool. P (W,R))`,
     MATCH_ACCEPT_TAC FORALL_PAIR_THM) in
  (end_itlist CONJ o map (REWRITE_RULE[pth] o GEN_ALL) o CONJUNCTS o
   new_recursive_definition form_RECURSION)
  `(holds WR V False (w:W) <=> F) /\
   (holds WR V True w <=> T) /\
   (holds WR V (Atom s) w <=> V s w) /\
   (holds WR V (Not p) w <=> ~(holds WR V p w)) /\
   (holds WR V (p && q) w <=> holds WR V p w /\ holds WR V q w) /\
   (holds WR V (p || q) w <=> holds WR V p w \/ holds WR V q w) /\
   (holds WR V (p --> q) w <=> holds WR V p w ==> holds WR V q w) /\
   (holds WR V (p <-> q) w <=> holds WR V p w <=> holds WR V q w) /\
   (holds WR V (Box p) w <=>
    !w'. w' IN FST WR /\ SND WR w w' ==> holds WR V p w')`;;
```
We say that a formula $p$ **holds in a certain frame** iff it holds in every world for every model of that frame. <br>
$\langle W, R\rangle \vDash p \iff \forall w \in W (\forall V (\langle W, R, V\rangle, w \vDash p$))
```
let holds_in = new_definition
  `holds_in (W,R) p <=> !V w:W. w IN W ==> holds (W,R) V p w`;;
```
We say that a formula $p$ is **valid in a class of frames** iff it holds in every frame of this class. <br>
$L \vDash p \iff \forall \langle W,R \rangle \in L (\langle W,R \rangle \vDash p)$
```
let valid = new_definition
  `L |= p <=> !f:(W->bool)#(W->W->bool). f IN L ==> holds_in f p`;;
```
The innovative definition of Kripke's model stands on the notion of **modal frame**, namely an ordered pair where the first object is a non-empty set (_domain of the possible worlds_) and the second one is a binary relation on the first set (_accessibility relation_).
```
let FRAME_DEF = new_definition
  `FRAME = {(W:W->bool,R:W->W->bool) | ~(W = {}) /\
                                       (!x y:W. R x y ==> x IN W /\ y IN W)}`;;
```
## Theory of Correspondence
We define the **set of frames correspondent to S**, i.e. the set of all the finite frames such that if p is a theorem of S, then p holds in this frame. <br>
{ $\langle W,R \rangle \in FINITE-FRAMES| \forall p (S \vdash p \implies \langle W,R \rangle \vDash p)$ }
```
let CORR_DEF = new_definition
  `CORR S = {(W:W->bool,R:W->W->bool) |
             (((W,R) IN FINITE_FRAME ) /\
             (!p. [S. {} |~ p] ==> holds_in (W:W->bool,R:W->W->bool) (p)))}`;;
```
For each one of the normal system S developed in HOLMS we prove what set of frames is correspondent to S ($C= CORR S$), then we prove that every frame that is in C is correspondent to S ($\subseteq$: $\forall F \in C(S \vdash p \implies F \vDash p)$ ) and that every frame that is correspondent to S is in C ($\supseteq$: $\forall F((S \vdash p \implies F \vDash p) \implies F \in C)$  ).

### K-Finite Frames 
We prove that the set of finite frames is the one correspondent to K.
```
FINITE_FRAME_CORR_K
 |-`FINITE_FRAME:(W->bool)#(W->W->bool)->bool = CORR {}`;; 
```
### T-Finite Reflexive Frames (RF)
We prove that the set of finite reflexive frames is the one correspondent to T.
```
let RF_DEF = new_definition
 `RF =
  {(W:W->bool,R:W->W->bool) |
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> R x x)}`;;

RF_CORR_T
 |-`FINITE_FRAME:(W->bool)#(W->W->bool)->bool = CORR {}`;;
```
### K4-Finite Transitive Frames (TF)
We prove that the set of finite transitive frames is the one correspondent to K4.
```
let TF_DEF = new_definition
 `TF =
  {(W:W->bool,R:W->W->bool) |
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

TF_CORR_K4
 |-`TF: (W->bool)#(W->W->bool)->bool = CORR K4_AX`;;
```
### GL-Finite Irreflexive and Transitive Frames (ITF)
We prove that the set of finite transitive and irreflexive frames is the one correspondent to GL.
```
let ITF_DEF = new_definition
  `ITF =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    FINITE W /\
    (!x. x IN W ==> ~R x x) /\
    (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

ITF_CORR_GL
 |-`ITF: (W->bool)#(W->W->bool)->bool = CORR GL_AX`;;
```

## Soundness and Consistency
We demonstrate the **soundness** of each S with respect to CORR S.
```
GEN_CORR_VALID
|- `!S p. [S. {} |~ p] ==> CORR S:(W->bool)#(W->W->bool)->bool |= p`;;
```

Then, by specializing the proof of `GEN_CORR_VALID`, we prove the soundness of each normal system  S developed in HOLMS with respect to its correspondent frame.
Moreover we prove its **consistency**, by modus ponens on the converse of `S_FRAME_VALID`.

### Soundness and consistency of K
```
let K_FINITE_FRAME_VALID = prove
(`!p. [{} . {} |~ p] ==> FINITE_FRAME:(W->bool)#(W->W->bool)->bool |= p`,
ASM_MESON_TAC[GEN_CORR_VALID; FINITE_FRAME_CORR_K]);;

let K_CONSISTENT = prove
 (`~ [{} . {} |~ False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] K_FINITE_FRAME_VALID)) THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM; IN_FINITE_FRAME; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;
```

### Soundness and consistency of T
```
let T_RF_VALID = prove
 (`!p. [T_AX . {} |~ p] ==> RF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_CORR_VALID; RF_CORR_T]);;

let T_CONSISTENT = prove
 (`~ [T_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] T_RF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_RF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. x = 0 /\ x = y`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;
```

### Soundness and consistency of K4
```
let K4_TF_VALID = prove
 (`!p. [K4_AX . {} |~ p] ==> TF:(W->bool)#(W->W->bool)->bool |= p`,
  MESON_TAC[GEN_CORR_VALID; TF_CORR_K4]);;

let K4_CONSISTENT = prove
 (`~ [K4_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] K4_TF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_TF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;
```

### Soundness and consistency of GL
```
let GL_ITF_VALID = prove
(`!p. [GL_AX . {} |~ p] ==> ITF:(W->bool)#(W->W->bool)->bool |= p`,
ASM_MESON_TAC[GEN_CORR_VALID; ITF_CORR_GL]);;

let GL_consistent = prove
 (`~ [GL_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] GL_ITF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_ITF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;
```

## Completeness theorems

### Proof Sketch (1)

Given a modal system $S$, we want to prove that it is **complete with respect to the set of its correspondent frames**: $\forall p (CORRS \vDash p \implies S \vdash p)$

```
S_COMPLETNESS_THM
|. `!p. ( CORR S |= p ==> [S. {} |~ p])`
```
**1. Rewriting `S_COMPLETNESS`'s statment** <br>
By using some tautologies and rewriting, we can show that the completeness theorem is equivalent to a more handy sentence:  <br>
$\forall p (S \not \vdash p \implies \exists \langle W,R\rangle_{S,p} \in CORR_S (\exists V_{S,p} \exists m_{S,p} \in W_{S,p} (\langle W_{S,p}, R_{S,p}, V_{S,p} \rangle, m_{S,p} \not \vDash p))$

A. We rewrite the sentence by _contraposition_. <br>
`e GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM];;` <br>

B. We rewrite validity in a set of frames (`valid`) as validity in a certain world of a certain model (`holds`) and we exploit some _propositional tautologies_. <br>
`e (REWRITE_TAC[valid; NOT_FORALL_THM; FORALL_PAIR_THM; holds_in; NOT_IMP]);;` <br>

```
S_COMPLETNESS_THM'
|- `!p. ( `~[S . {} |~ p] ==>
          (exists W R. W,R IN CORR S /\
            (exists V m. m IN p1 /\
              ~holds (p1,p2) V p w)))`
```

At this point, for each modal formula $p$ we need to construct a **_countermodel_** $𝓜_{S,p}$ and a "**_counterworld_**" $m_{S,p}$ in the domain of the countermodel.

We can observe that, by working with HOL, it is possible to identify all those lines of reasoning that are _parametric_ with respect to $S$ (the axiom system) and to  $p$ (the formula we are analysing) and develop te proof while avoiding code duplication as much as possible.

**2. Reducing a model theoretic-notion to a set/list-theoretic concept** 
The canonical proof of completeness, illustrated in classical textbooks like George Boolos's "The Logic of Provability", exploit the idea of working in a context (_countermodel_) such that: $\forall w \in W_{S,p} (w \in p \iff 𝓜_{S,p},w \vDash p) $.

Observe that, in such a context, the members of the domain $W_{S,p}$ are set (list in HOLMS) of modal formulas.
If we are able to construct a countermodel with this constraints, we will easily construct a counterworld $m_{S,p}$ that is a set of formulas not including p.

Then our subgoal would be to prove: <br> 
```
S_COMPLETNESS_THM''
|- `!p. ( `~[S . {} |~ p] ==>
          (exists W R. W,R IN CORR S /\
            (exists M. M IN p1 /\
              ~ MEM p M)))`
```

 This subgoal is much more manageable than the previous statement, indeed it reduces the **model-theoretic** notion of _validity_ (`holds (W,R) V p w`) to the **set-theoretic** concept (**list-theoretic** in HOLMS) of _membership_ (`MEM p w`).


**3. What do we need to prove?** <br>
Given our aim of proving $\forall p(S \not \vdash p \implies \exists \langle W,R \rangle_{S,p} \in CORR S(\exists m_{S,p} \in W_{S,p}(p \not \in m_{S,p})))$, we need a countermodel and counterworld following these constraints: 

A. The Kripke's frame $\langle W,R \rangle_{S,p}$ must be **correspondent** to S. <br>
$\langle W,R \rangle_{S,p} \in CORRS$ <br>

B. The Kripke's model $𝓜_{S,p} = \langle W,R,V \rangle_{S,p}$ must allows us to **reduce validity to membership**. <br>
Namely, for our model $𝓜_{S,p}$ holds $\forall w \in W_{S,p} (w \in p \iff 𝓜_{S,p},w \vDash p) $. 

C. The counterworld $m_{S,p}$ must not contain p. <br>
$p \not \in m_{S,p}$

D. Consequently $W_{S,p}$ must be a **set of formula's lists** <br>
`CORRS:(form list->bool)#(form list->form list->bool)->bool`. 

### The Proof (1)

The first part of the proof is organized in three steps.

### STEP 1
Identification of a model <W,R,V> depending on a formula p and, in particular, of a non-empty set of possible worlds given by a subclass of maximal consistent sets of formulas.

Parametric Definitions in `gen_completeness.ml` (parameters P, S)
```
let FRAME_DEF = new_definition
  `FRAME = {(W:W->bool,R:W->W->bool) | ~(W = {}) /\
                                       (!x y:W. R x y ==> x IN W /\ y IN W)}`;;

let GEN_STANDARD_FRAME_DEF = new_definition
  `GEN_STANDARD_FRAME P S p =
   FRAME INTER P INTER
   {(W,R) | W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))}`;;

let GEN_STANDARD_MODEL_DEF = new_definition
  `GEN_STANDARD_MODEL P S p (W,R) V <=>
   (W,R) IN GEN_STANDARD_FRAME P S p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;
```

Definitions in `k_completeness.ml` (P=FINITE_FRAME, S={})
```
let K_STANDARD_FRAME_DEF = new_definition
  `K_STANDARD_FRAME = GEN_STANDARD_FRAME {}`;;

IN_K_STANDARD_FRAME
|- `(W,R) IN K_STANDARD_FRAME p <=>
W = {w | MAXIMAL_CONSISTENT {} p w /\
         (!q. MEM q w ==> q SUBSENTENCE p)} /\
(W,R) IN FINITE_FRAME /\
(!q w. Box q SUBFORMULA p /\ w IN W
       ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`

K_STANDARD_MODEL_CAR
|- `K_STANDARD_MODEL p (W,R) V <=>
   (W,R) IN K_STANDARD_FRAME p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`
let K_STANDARD_MODEL_DEF = new_definition
   `K_STANDARD_MODEL = GEN_STANDARD_MODEL {}`;;

```

Definitions in `t_completeness.ml` (P=FINITE_FRAME, S=T_AX})
```
let T_STANDARD_FRAME_DEF = new_definition
`T_STANDARD_FRAME p = GEN_STANDARD_FRAME T_AX p`;;  

IN_T_STANDARD_FRAME 
|- `!p W R. (W,R) IN T_STANDARD_FRAME p <=>
          W = {w | MAXIMAL_CONSISTENT T_AX p w /\
                   (!q. MEM q w ==> q SUBSENTENCE p)} /\
          (W,R) IN RF /\
          (!q w. Box q SUBFORMULA p /\ w IN W
                 ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`

let T_STANDARD_MODEL_DEF = new_definition
   `T_STANDARD_MODEL = GEN_STANDARD_MODEL T_AX`;;

T_STANDARD_MODEL_CAR
|- `!W R p V.
     T_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN T_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`
```

Definitions in `k4_completeness.ml` (P=FINITE_FRAME, S=T_AX})
```
let K4_STANDARD_FRAME_DEF = new_definition
`K4_STANDARD_FRAME p = GEN_STANDARD_FRAME K4_AX p`;;  

IN_K4_STANDARD_FRAME
|- (`!p W R. (W,R) IN K4_STANDARD_FRAME p <=>
          W = {w | MAXIMAL_CONSISTENT K4_AX p w /\
                   (!q. MEM q w ==> q SUBSENTENCE p)} /\
          (W,R) IN TF /\
          (!q w. Box q SUBFORMULA p /\ w IN W
                 ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`

let K4_STANDARD_MODEL_DEF = new_definition
   `K4_STANDARD_MODEL = GEN_STANDARD_MODEL K4_AX`;;

K4_STANDARD_MODEL_CAR
|- (`!W R p V.
     K4_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN K4_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`,
```

Definitions in `gl_completeness.ml` (P=ITF, S=GL_AX)
```
let ITF_DEF = new_definition
  `ITF =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    FINITE W /\
    (!x. x IN W ==> ~R x x) /\
    (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

let GL_STANDARD_FRAME_DEF = new_definition
  `GL_STANDARD_FRAME p = GEN_STANDARD_FRAME ITF GL_AX p`;;

IN_GL_STANDARD_FRAME
|- !p W R. (W,R) IN GL_STANDARD_FRAME p <=>
           W = {w | MAXIMAL_CONSISTENT GL_AX p w /\
                    (!q. MEM q w ==> q SUBSENTENCE p)} /\
           (W,R) IN ITF /\
           (!q w. Box q SUBFORMULA p /\ w IN W
                  ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))

let GL_STANDARD_MODEL_DEF = new_definition
  `GL_STANDARD_MODEL = GEN_STANDARD_MODEL ITF GL_AX`;;

GL_STANDARD_MODEL_CAR
|- !W R p V.
     GL_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN GL_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))
```

### STEP 2
Definition of a “standard” accessibility relation depending on axiom set S between these worlds such that the frame is appropriate to S.

Parametric definition of the standard relation in `gen_completeness.ml` (parameter S)
```
let GEN_STANDARD_REL = new_definition
  `GEN_STANDARD_REL S p w x <=>
   MAXIMAL_CONSISTENT S p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT S p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;
```

Definitions in `k_completeness.ml` (S={}) and proof of the Accessibility Lemma for K.
```
let K_STANDARD_REL_DEF = new_definition
  `K_STANDARD_REL p = GEN_STANDARD_REL {} p`;;

K_STANDARD_REL_CAR
|- K_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT {} p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT {} p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)

K_ACCESSIBILITY_LEMMA_1
|- !p w q. ~ [{} . {} |~ p] /\
           MAXIMAL_CONSISTENT {} p w /\
           (!q. MEM q w ==> q SUBSENTENCE p) /\
           Box q SUBFORMULA p /\
           (!x. K_STANDARD_REL p w x ==> MEM q x)
           ==> MEM (Box q) w
```

Definitions in `gl_completeness.ml` (S=GL_AX) and proofs of the Accessibility Lemma for GL.
```
let GL_STANDARD_REL_DEF = new_definition
  `GL_STANDARD_REL p w x <=>
   GEN_STANDARD_REL GL_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

GL_ACCESSIBILITY_LEMMA
|- !p M w q.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p M /\
     (!q. MEM q M ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT GL_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     MEM (Not p) M /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w
```

### STEP 3
The reduction of the notion of forcing `holds (W,R) V q w` to that of a set-theoretic (list-theoretic) membership MEM q w
for every subformula q of p, through a specific atomic evaluation function on (W,R).

Parametric truth lemma in `gen_completeness.ml` (parameters P, S)
```
GEN_TRUTH_LEMMA
|- !P S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL P S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)
```

Truth lemma specified for K in `k_completeness.ml` (P=K_FRAME, S={})
```
let K_TRUTH_LEMMA = prove
 (`!W R p V q.
     ~ [{} . {} |~ p] /\
     K_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[K_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;
```

Truth lemma specified for GL in `gl_completeness.ml` (P=ITF, S=GL_AX)
```
let GL_truth_lemma = prove
 (`!W R p V q.
     ~ [GL_AX . {} |~ p] /\
     GL_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REWRITE_TAC[GL_STANDARD_MODEL_DEF] THEN MESON_TAC[GEN_TRUTH_LEMMA]);;
```

### The Theorems

Completeness of K in `k_completeness.ml`.
This proof uses the `K_TRUTH_LEMMA` that specifies the `GEN_TRUTH_LEMMA`, therefore the first part of the proof of the completeness theorem for K is completely parametrized.
```
K_COMPLETENESS_THM
|- !p. K_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]
```

Completeness of GL in `gl_completeness.ml`
This proof uses the `GL_TRUTH_LEMMA` that specifies the `GEN_TRUTH_LEMMA`, therefore the first part of the proof of the completeness theorem for GL is completely parametrized.
```
GL_COMPLETENESS_THM
|- !p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [GL_AX . {} |~ p]
```

###  Modal completeness for models on a generic (infinite) domain.
Thanks to the parametric lemma `GEN_LEMMA_FOR_GEN_COMPLETENESS`, we quickly generalize for each normal system the completeness theorem for models with infinite worlds. <br>
In `gen_completeness`.
```
GEN_LEMMA_FOR_GEN_COMPLETENESS
|- `!S. INFINITE (:A)
       ==> !p. CORR S:(A->bool)#(A->A->bool)->bool |= p
            ==> CORR S:(form list->bool)#(form list->form list->bool)->bool |= p`;;
```
As corollaries of `GEN_LEMMA_FOR_GEN_COMPLETENESS` in the specific files.
```
K_COMPLETENESS_THM_GEN
|- `!p. INFINITE (:A) /\ FINITE_FRAME:(A->bool)#(A->A->bool)->bool |= p
       ==> [{} . {} |~ p]`

T_COMPLETENESS_THM_GEN
|- `!p. INFINITE (:A) /\ RF:(A->bool)#(A->A->bool)->bool |= p
       ==> [T_AX . {} |~ p]`

K4_COMPLETENESS_THM_GEN
|- `!p. INFINITE (:A) /\ TF:(A->bool)#(A->A->bool)->bool |= p
       ==> [K4_AX . {} |~ p]`

GL_COMPLETENESS_THM_GEN
|- !p. INFINITE (:A) /\ ITF:(A->bool)#(A->A->bool)->bool |= p
       ==> [GL_AX . {} |~ p]
```


## Finite model property and decidability

### In K
Construction of the countermodels.
```
let K_STDWORLDS_RULES,K_STDWORLDS_INDUCT,K_STDWORLDS_CASES = new_inductive_set
  `!M. MAXIMAL_CONSISTENT {} p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN K_STDWORLDS p`;;

let K_STDREL_RULES,K_STDREL_INDUCT,K_STDREL_CASES = new_inductive_definition
  `!w1 w2. K_STANDARD_REL p w1 w2
           ==> K_STDREL p (set_of_list w1) (set_of_list w2)`;;
```

Theorem of existence of the finite countermodel.
```
k_COUNTERMODEL_FINITE_SETS
|- !p. ~[{} . {} |~ p] ==> ~holds_in (K_STDWORLDS p, K_STDREL p) p
```

### In GL
Construction of the countermodels.
```
let GL_STDWORLDS_RULES,GL_STDWORLDS_INDUCT,GL_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT GL_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN GL_STDWORLDS p`;;

let GL_STDREL_RULES,GL_STDREL_INDUCT,GL_STDREL_CASES = new_inductive_definition
  `!w1 w2. GL_STANDARD_REL p w1 w2
           ==> GL_STDREL p (set_of_list w1) (set_of_list w2)`;;
```

Theorem of existence of the finite countermodel.
```
GL_COUNTERMODEL_FINITE_SETS
|- !p. ~ [GL_AX . {} |~ p] ==> ~holds_in (GL_STDWORLDS p, GL_STDREL p) p
```

## Automated theorem proving and countermodel construction

### In K

Our tactic `K_TAC` and its associated rule `K_RULE` can automatically prove theorems in the modal logic K.

Examples:
```
K_RULE `!a b. [{} . {} |~ Box (a && b) <-> Box a && Box b]`;;

K_RULE `!a b. [{} . {} |~ Box a || Box b --> Box (a || b)]`;;
```


### In T

Our tactic `T_TAC` and its associated rule `T_RULE` can automatically prove theorems in the modal logic T.

Examples:
```
T_RULE `!a. [ T_AX . {} |~ a --> Diamond a ]`;;
T_RULE `!a. [ T_AX . {} |~ Box a --> Diamond a ]`;;
```

### In K4

Our tactic `K4_TAC` and its associated rule `K4_RULE` can automatically prove theorems in the modal logic K4.

### Example of a formula valid in K4 but not in K
```
time GL_RULE
  `!a. [GL_AX . {} |~ Box Diam Box Diam a <-> Box Diam a]`;;
```


### In GL

Our tactic `GL_TAC` and its associated rule `GL_RULE` can automatically prove theorems in the modal logic GL.
Here is a list of examples

### Example of a formula valid in GL but not in K
```
time GL_RULE
  `!a. [GL_AX . {} |~ Box Diam Box Diam a <-> Box Diam a]`;;
```

### Formalised Second Incompleteness Theorem
In PA, the following is provable: If PA is consistent, it cannot prove its own consistency.
```
let GL_second_incompleteness_theorem = time GL_RULE
  `[GL_AX . {} |~ Not (Box False) --> Not (Box (Diam True))]`;;
```

### PA ignores unprovability statements
```
let GL_PA_ignorance = time GL_RULE
  `!p. [GL_AX . {} |~ (Box False) <-> Box (Diam p)]`;;
```

### PA undecidability of consistency
If PA does not prove its inconsistency, then its consistency is undecidable.
```
let GL_PA_undecidability_of_consistency = time GL_RULE
  `[GL_AX . {} |~ Not (Box (Box False))
                  --> Not (Box (Not (Box False))) &&
                      Not (Box (Not (Not (Box False))))]`;;
```
### Undecidability of Gödels formula
```
let GL_undecidability_of_Godels_formula = time GL_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) && Not (Box (Box False))
                      --> Not (Box p) && Not (Box (Not p))]`;;
```

### Reflection and iterated consistency
If a reflection principle implies the second iterated consistency assertion, then the converse implication holds too.
```
let GL_reflection_and_iterated_consistency = time GL_RULE
  `!p. [GL_AX . {} |~ Box ((Box p --> p) --> Diam (Diam True))
                      --> (Diam (Diam True) --> (Box p --> p))]`;;
```

### A Godel sentence is equiconsistent with a consistency statement
```
let GL_Godel_sentence_equiconsistent_consistency = time GL_RULE
  `!p. [GL_AX . {} |~ Box (p <-> Not (Box p)) <->
                      Box (p <-> Not (Box False))]`;;
```

### Arithmetical fixpoint
For any arithmetical sentences p q, p is equivalent to unprovability of q --> p iff p is equivalent to consistency of q.
```
let GL_arithmetical_fixpoint = time GL_RULE
  `!p q. [GL_AX . {} |~ Dotbox (p <-> Not (Box (q --> p))) <->
                        Dotbox (p <-> Diam q)]`;;
```
