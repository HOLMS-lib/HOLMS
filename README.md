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
We first sketch the idea behind the demonstration and, then, we will presnt a three-steps proof.

### The Idea behind the Proof

Given a modal system $S$, we want to prove that it is **complete with respect to the set of its correspondent frames**: $\forall p (CORRS \vDash p \implies S \vdash p)$

```
S_COMPLETNESS_THM
|. `!p. ( CORR S |= p ==> [S. {} |~ p])`
```
- **1. Rewriting `S_COMPLETNESS`'s statment** <br>
By using some tautologies and rewriting, we can show that the completeness theorem is equivalent to a more handy sentence:  <br>
$\forall p (S \not \vdash p \implies \exists \langle W,R\rangle_{S,p} \in CORR_S (\exists V_{S,p} \exists m_{S,p} \in W_{S,p} (\langle W_{S,p}, R_{S,p}, V_{S,p} \rangle, m_{S,p} \not \vDash p))$ <br> <br>
  - A. We rewrite the sentence by _contraposition_. <br>
   `e GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM];;` <br> <br>
  - B. We rewrite validity in a set of frames (`valid`) as validity in a certain world of a certain model (`holds`) and we exploit some _propositional tautologies_. <br>
   `e (REWRITE_TAC[valid; NOT_FORALL_THM; FORALL_PAIR_THM; holds_in; NOT_IMP]);;` <br>
```
S_COMPLETNESS_THM'
|- `!p. ( `~[S . {} |~ p] ==>
          (exists W R. W,R IN CORR S /\
            (exists V m. m IN p1 /\
              ~holds (p1,p2) V p w)))`
```
At this point, for each modal formula $p$ we need to construct a **_countermodel_** $𝓜_{S,p}$ and a "**_counterworld_**" $m_{S,p}$ in the domain of the countermodel. <br> <br>
We can observe that, by working with HOL, it is possible to identify all those lines of reasoning that are _parametric_ with respect to $S$ (the axiom system) and to  $p$ (the formula we are analysing) and develop te proof while avoiding code duplication as much as possible. <br>
<br>
- **2. Reducing a model theoretic-notion to a set/list-theoretic concept** 
The canonical proof of completeness, illustrated in classical textbooks like George Boolos's "The Logic of Provability", exploit the idea of working in a context (_countermodel_) such that: $\forall w \in W_{S,p} (w \in p \iff 𝓜_{S,p},w \vDash p) $. <br> <br>
Observe that, in such a context, the members of the domain $W_{S,p}$ are set (list in HOLMS) of modal formulas.
If we are able to construct a countermodel with this constraints, we will easily construct a counterworld $m_{S,p}$ that is a set of formulas not including p.
<br> <br>
Then our subgoal would be to prove: <br> 
```
S_COMPLETNESS_THM''
|- `!p. ( `~[S . {} |~ p] ==>
          (exists W R. W,R IN CORR S /\
            (exists M. M IN p1 /\
              ~ MEM p M)))`
```
This subgoal is much more manageable than the previous statement, indeed it reduces the **model-theoretic** notion of _validity_ (`holds (W,R) V p w`) to the **set-theoretic** concept (**list-theoretic** in HOLMS) of _membership_ (`MEM p w`).


- **3. What do we need to prove?** <br>
Given our aim of proving $\forall p(S \not \vdash p \implies \exists \langle W,R \rangle_{S,p} \in CORR S(\exists m_{S,p} \in W_{S,p}(p \not \in m_{S,p})))$, we need a countermodel and counterworld following these constraints: <br> <br>
  - A. The Kripke's frame $\langle W,R \rangle_{S,p}$ must be **correspondent** to S. <br>
    $\langle W,R \rangle_{S,p} \in CORRS$ <br> <br>
  - B. The Kripke's model $𝓜_{S,p} = \langle W,R,V \rangle_{S,p}$ must allows us to **reduce validity to membership**. <br>
    Namely, for our model $𝓜_{S,p}$ holds $\forall w \in W_{S,p} (w \in p \iff 𝓜_{S,p},w \vDash p) $. <br> <br>
  - C. The counterworld $m_{S,p}$ must not contain p. <br>
      $p \not \in m_{S,p}$ <br> <br>
  - D. Consequently $W_{S,p}$ must be a **set of formula's lists** <br>
   `CORRS:(form list->bool)#(form list->form list->bool)->bool`. 


### STEP 1: Partial definition of a parametric Standard Model 

We partially identify the countermodel $𝓜_{S,p} = \langle W,R,V \rangle_{S,p}$ by defining $W_{S,p}$ as a set of maximal consistent lists, $V$as a particular binary relation over formulas' atoms and worlds and by requesting two constraints for $R_{S,p}$. The definition of 'STANDARD_MODEL` in step 1 is fully parametric.

Before this construction of the countermodel, we defined in `consistent.ml` some properties that hold for formulas' lists.

#### Consistent $S$ 
A list of formulas $X$ is consistent to a set of axioms $S$ iff and only if $S \not \vdash \neg \bigwedge X$
```
let CONSISTENT = new_definition
  `CONSISTENT S (X:form list) <=> ~[S . {} |~ Not (CONJLIST X)]`;;
```

#### Maximal Consistent $S,p$ <br>
A list of formulas $X$ is maximal-consistent to a set of axioms $S$ and modal formula $p$ iff X has no repetitions, X is consistent $_S$ and $\forall q (q \ subformula \ p \implies q \in X \lor \neg q \in l)$.
```
let MAXIMAL_CONSISTENT = new_definition
  `MAXIMAL_CONSISTENT S p X <=>
   CONSISTENT S X /\ NOREPETITION X /\
   (!q. q SUBFORMULA p ==> MEM q X \/ MEM (Not q) X)`;;
```

#### Lemma of Extension of Maximal Consistent lists
$X \ Consistent_S \implies \exists M (X \subseteq M \ \land \ M \ Maximal-Consistent_{S,p} )$
```
EXTEND_MAXIMAL_CONSISTENT 
|- (`!S p X. CONSISTENT S X /\
           (!q. MEM q X ==> q SUBSENTENCE p)
           ==> ?M. MAXIMAL_CONSISTENT S p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p) /\
                   X SUBLIST M`
```

Then we define a **standard model** such that:

- **A: The Domain $W_{S,p}$  is $ { $X | Maximal-Consistent_{S,p} \ X $ }** <br> <br>
  As requested the domain is a set of list of formulas and, in particular, it is a subclass of maximal consistent sets of formulas. <br>
  Observe that, in principle, we can employ general **sets** of formulas in the formalisation. However, from the practical viewpoint, **lists without repetitions** are better
suited since they are automatically finite and we can easily manipulate them by structural recursion. <br> <br>
We prove, as requested for the domain of a frame, that $W_{S,p}$ is non-empty by using `NONEMPTY_MAXIMAL_CONSISTENT`, a corollary of the lemma of extension of maximal consistent lists.
```
NONEMPTY_MAXIMAL_CONSISTENT
|- `!S p. ~ [S . {} |~ p]
         ==> ?M. MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)`
```

- **B: The Accessibility Relation $R_{S,p}$** should meet two conditions
   - R1: $\forall q \in Form_{\Box} (\Box q \ subformula \ p \implies \forall w \in W_{S,p}(\Box q \in w \iff \forall x (wRx \implies q \in x)))$. <br>
     This condition ensures that my list-theoretic translation follows kripke's semantics.
   - R2: $\langle W,R \rangle_{S,p} \in CORR S$. <br>
    This second condition guarantees one of the four initial constraints.

- **C: The Evaluation Relation $R_{S,p}$** is defined as follows <br>
  $\forall m \in W_{S,p} \ \forall a \in Atom-Form_{\Box} (mVa \iff a \ subformula \ p \land a \in m)$


In particular, in HOLMS `gen_completeness.ml` we develop a parametric (to S and p) definition  of `GEN_STANDARD_FRAME` and `GEN_STANDARD_MODEL` and then we specialize these definitions for each normal system. 

```
let GEN_STANDARD_FRAME_DEF = new_definition
  `GEN_STANDARD_FRAME S p =
   CORR S INTER
   {(W,R) | W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))}`;;

let GEN_STANDARD_MODEL_DEF = new_definition
  `GEN_STANDARD_MODEL S p (W,R) V <=>
   (W,R) IN GEN_STANDARD_FRAME S p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;
```
Because the definitions of `K_STANDARD_MODEL`, `T_STANDARD_MODEL`, `K4_STANDARD_MODEL` and `GL_STANDARD_MODEL` are a simple specification of `GEN_STANDARD_FRAME` and `GEN_STANDARD_MODEL` with the parameters `{}`, `T_AX`, `K4_AX` and `GL_AX`, we present here just the definitions for $K4$.

Definitions in `k4_completeness.ml` (`S`=`K4_AX`)
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


### STEP 2: Definition of a standard accessibility relation for each S
The definition of a standard acessibility relation cannot be fully parametrized, at least following the approach presented in classical textbook.

Consequently, to avoid code repetions in `gen_completeness.ml` we will define a `GEN_STANDARD_REL` that is parametric to $S$ and $p$, but then we will complete the definition of the standard relation for each normal system in the spefic file of each system `S_completeness.ml` in a way that guarantees that conditions R1 and R2 holds. 

After we have defined the `S_STANDARD_REL` we will show:
- The most difficult verse of R1's implication in `S_ACCESSIBILITY_LEMMA` <br>
$\forall q \in Form_{\Box} (\Box q \ subformula \ p \implies \forall w \in W_{S,p}(\Box q \in w \Longleftarrow \forall x (wRx \implies q \in x)))$
-   R2 holds for $\langle W_{S,p},$ _S_STANDARD_REL_ $\rangle$ in ` S_MAXIMAL_CONSISTENT`. <br>
    $\langle W_{S,p},$ _S_STANDARD_REL_ $\rangle  \in CORRS$
    
Then `SF_IN_STANDARD_S_FRAME` follows as corollary and, given the hypotesis that $S \not \vdash p$,  $\langle W_{S,p},$ S_STANDARD_REL $, V_{S,p} \rangle$ is an `S_STANDARD_MODEL`.

#### Parametric definition of the standard relation in `gen_completeness`.
```
let GEN_STANDARD_REL = new_definition
  `GEN_STANDARD_REL S p w x <=>
   MAXIMAL_CONSISTENT S p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT S p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;
```

#### Definition of the standard relation for K in `k_completeness.ml`.
```
let K_STANDARD_REL_DEF = new_definition
  `K_STANDARD_REL p = GEN_STANDARD_REL {} p`;;

K_STANDARD_REL_CAR
|- `K_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT {} p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT {} p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`
```

**Accessibility Lemma for K** that ensures the most difficult verse of R1's implication.
```
K_ACCESSIBILITY_LEMMA
|- `!p w q. ~ [{} . {} |~ p] /\
         MAXIMAL_CONSISTENT {} p w /\
         (!q. MEM q w ==> q SUBSENTENCE p) /\
         Box q SUBFORMULA p /\
         (!x. K_STANDARD_REL p w x ==> MEM q x)
         ==> MEM (Box q) w`
```
**Maximal Consistent Lemma for K** that ensures R2.
```
K_MAXIMAL_CONSISTENT
|- (`!p. ~ [{} . {} |~ p]
     ==> ({M | MAXIMAL_CONSISTENT {} p M /\
          (!q. MEM q M ==> q SUBSENTENCE p)},
          K_STANDARD_REL p) IN FINITE_FRAME`,
```
Proof of the corollary that ensures that **our construction for K is a standard frame**.
```
g `!p. ~ [{} . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT {} p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}, 
             K_STANDARD_REL p) IN K_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC [IN_K_STANDARD_FRAME]);;
e CONJ_TAC;;
e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (INTRO_TAC "!q w; subform w_in");;
e EQ_TAC;;
 e (ASM_MESON_TAC[K_STANDARD_REL_CAR]);;
 e (INTRO_TAC "Implies_Mem_q");;
   e (HYP_TAC "w_in" (REWRITE_RULE[IN_ELIM_THM]));;
   e (MATCH_MP_TAC K_ACCESSIBILITY_LEMMA);;
   e (EXISTS_TAC `p:form`);;
   e (ASM_REWRITE_TAC[]);;
let KF_IN_STANDARD_K_FRAME = top_thm();;
```


#### Definition of the standard relation for T in `t_completeness.ml`.
```
let T_STANDARD_REL_DEF = new_definition
  `T_STANDARD_REL p w x <=>
   GEN_STANDARD_REL T_AX p w x`;;

T_STANDARD_REL_CAR
|- `!p w x.
     T_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT T_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT T_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM B x)`
```

**Accessibility Lemma for T** that ensures the most difficult verse of R1's implication.
```
T_ACCESSIBILITY_LEMMA
|- `!p w q.
   ~ [T_AX . {} |~ p] /\
   MAXIMAL_CONSISTENT T_AX p w /\
   (!q. MEM q w ==> q SUBSENTENCE p) /\
   Box q SUBFORMULA p /\
   (!x. T_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`
```
**Maximal Consistent Lemma for T** that ensures R2.
```
RF_MAXIMAL_CONSISTENT
|- `!p. ~ [T_AX . {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT T_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                   T_STANDARD_REL p) IN RF `
```
Proof of the corollary that ensures that **our construction for T is a standard frame**.
```
g `!p. ~ [T_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT T_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}, 
             T_STANDARD_REL p) IN T_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC [IN_T_STANDARD_FRAME]);;
e CONJ_TAC;;
e (MATCH_MP_TAC RF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; boxq maxw subw");;
e EQ_TAC;;
 e (ASM_MESON_TAC[T_STANDARD_REL_CAR]);;
 e (ASM_MESON_TAC[T_ACCESSIBILITY_LEMMA]);;
let RF_IN_T_STANDARD_FRAME = top_thm();;
```
#### Definition of the standard relation for K4 in `k4_completeness.ml`.
```
let K4_STANDARD_REL_DEF = new_definition
  `K4_STANDARD_REL p w x <=>
   GEN_STANDARD_REL K4_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x)`;;

K4_STANDARD_REL_CAR
|- `!p w x.
     K4_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT K4_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT K4_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM (Box B) x /\ MEM B x)`
```

**Accessibility Lemma for K4** that ensures the most difficult verse of R1's implication.
```
K4_ACCESSIBILITY_LEMMA
|- `!p w q.
    ~ [K4_AX . {} |~ p] /\
    MAXIMAL_CONSISTENT K4_AX p w /\
    (!q. MEM q w ==> q SUBSENTENCE p) /\
    Box q SUBFORMULA p /\
    (!x. K4_STANDARD_REL p w x ==> MEM q x)
      ==> MEM (Box q) w`
```
**Maximal Consistent Lemma for K4** that ensures R2.
```
TF_MAXIMAL_CONSISTENT
|- `!p. ~ [T_AX . {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT T_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                   T_STANDARD_REL p) IN RF `
```
Proof of the corollary that ensures that **our construction for K4 is a standard frame**.
```
g `!p. ~ [K4_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT K4_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}, 
             K4_STANDARD_REL p) IN K4_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC [IN_K4_STANDARD_FRAME]);;
e CONJ_TAC;;
e (MATCH_MP_TAC TF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; boxq maxw subw");;
e EQ_TAC;;
 e (ASM_MESON_TAC[K4_STANDARD_REL_CAR]);;
 e (ASM_MESON_TAC[K4_ACCESSIBILITY_LEMMA]);;
let K4F_IN_K4_STANDARD_FRAME = top_thm();;
```

#### Definition of the standard relation for GL in `gl_completeness.ml`.
```
let GL_STANDARD_REL_DEF = new_definition
  `GL_STANDARD_REL p w x <=>
   GEN_STANDARD_REL GL_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

GL_STANDARD_REL_CAR
|- `!p w x.
     GL_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT GL_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT GL_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM (Box B) x /\ MEM B x) /\
     (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`
```

**Accessibility Lemma for GL** that ensures the most difficult verse of R1's implication.
```
GL_ACCESSIBILITY_LEMMA
|- `!p w q.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`
```
**Maximal Consistent Lemma for GL** that ensures R2.
```
ITF_MAXIMAL_CONSISTENT
|- `!p. ~ [GL_AX . {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT GL_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                   GL_STANDARD_REL p) IN ITF `
```
Proof of the corollary that ensures that **our construction for GL is a standard frame**.
```
g `!p. ~ [GL_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT GL_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}, 
             GL_STANDARD_REL p) IN GL_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC [IN_GL_STANDARD_FRAME]);;
e CONJ_TAC;;
e (MATCH_MP_TAC ITF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (INTRO_TAC "!q w; subform max_cons_w implies_w");;
e EQ_TAC;;
 e (ASM_MESON_TAC[GL_STANDARD_REL_CAR]);;
 e (ASM_MESON_TAC[GL_ACCESSIBILITY_LEMMA]);;
let GLF_IN_GL_STANDARD_FRAME = top_thm();;
```


### STEP 3: Proving the truth lemma
In this step we prove that, given a standard model and $S \not \vdash p$, the _desiderandum_ in the proof sketch holds, and indeed something stronger holds. <br>
_For every subformula q of p_ we can reduce the notion of forcing `holds (W,R) V q w` to that of a set-theoretic (list-theoretic) membership `MEM q w`.

Observe that we prove this foundamental lemma in a fully parametric way and, moreover, the proof of completness does not need to specify this lemma for our normal system in analysis. 

#### Parametric truth lemma in `gen_completeness.ml` (parameters P, S)
```
GEN_TRUTH_LEMMA
|- `!S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`
```

### The Theorems

At this point we built up a _countermodel_ $\langle W,R,V \rangle_{S,p}$ that is a _standard model for S_ and we want to prove that a counterworld in this model exists: <br>
 $\exist M_{S,p} \in W_{S,p} (p \not \in M_{S,p} )$ 

 So we need an $M_{S,p}$ such that:
 - A: $M_{S,p} \in W_{S,p}$ that is $Maximal_Consistent_{S,p} M$;
 - B: $p \not \in M_{S,p}$

But thanks to our theorem `NONEMPTY_MAXIMAL_CONSISTENT` $\forall p (S \vdash p \implies (\exists M (Maximal_Consistent_{S,p} M \land \neg p \in M))$, <br> we know that such an $M_{S,p}$ exists and we can prove `GEN_COUNTERMODEL_ALT`. Observe, indeed, that $Maximal_Consistent_{S,p} M \land \neg p \in M \implies p \not \in M_{S,p}$.
```
NONEMPTY_MAXIMAL_CONSISTENT
|- `!S p. ~ [S . {} |~ p]
         ==> ?M. MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)`


g `!S W R p. ~ [S . {} |~ p] /\
             (W,R) IN GEN_STANDARD_FRAME S p
             ==>
             ~holds_in (W,R) p`;;
e (INTRO_TAC "!S W R p; p_not_theor in_standard_frame");;
e (REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM]);;
e (EXISTS_TAC `\a M. Atom a SUBFORMULA p /\ MEM (Atom a) M`);;
e (DESTRUCT_TAC "@M. max mem subf" (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ [S . {} |~ p]`)));;
e (EXISTS_TAC `M:form list` THEN ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `GEN_STANDARD_MODEL S p (W,R) (\a M. Atom a SUBFORMULA p /\ MEM (Atom a) M) ` MP_TAC);;
e (ASM_MESON_TAC[GEN_STANDARD_MODEL_DEF]);;
e (INTRO_TAC "standard_model");;
e CONJ_TAC;;
e (HYP_TAC "in_standard_frame" (REWRITE_RULE[IN_GEN_STANDARD_FRAME]));;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (MP_TAC (ISPECL
     [`S: form ->bool`;
      `W: (form)list->bool`;
      `R: (form)list-> (form)list ->bool`;
      `p:form`;
      `(\a M. Atom a SUBFORMULA p /\ MEM (Atom a) M):((char)list->(form)list->bool)`;
      `p:form`] GEN_TRUTH_LEMMA));;
e (ANTS_TAC );;
e (ASM_REWRITE_TAC[SUBFORMULA_REFL]);;
e (DISCH_THEN (MP_TAC o SPEC `M:form list`));;
e ANTS_TAC;;
e (HYP_TAC "standard_model" (REWRITE_RULE[GEN_STANDARD_MODEL_DEF; IN_GEN_STANDARD_FRAME]));;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (DISCH_THEN (SUBST1_TAC o GSYM));;
e (ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;
let GEN_COUNTERMODEL_ALT = top_thm();;
```

Given the fully parametrized `GEN_COUNTERMODEL_ALT` and `SF_IN_STANDARD_S_FRAME`, the completeness theorems for each $S$ follow and their proofs are so short that we can present them here.

#### Completeness of K in `k_completeness.ml`.
```
g `!p. FINITE_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] );;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT {} p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                K_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC );;
e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT {} p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                  K_STANDARD_REL p) IN GEN_STANDARD_FRAME {} p`
                 MP_TAC);;
e (ASM_MESON_TAC[KF_IN_STANDARD_K_FRAME; K_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let K_COMPLETENESS_THM = top_thm ();;
```

#### Completeness of T in `t_completeness.ml`
```
g `!p. RF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [T_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] );;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT T_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                T_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC );;
e (MATCH_MP_TAC RF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT T_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                  T_STANDARD_REL p) IN GEN_STANDARD_FRAME T_AX p`
                 MP_TAC);;
e (ASM_MESON_TAC[RF_IN_T_STANDARD_FRAME; T_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let T_COMPLETENESS_THM = top_thm ();;
```

#### Completeness of K4 in `k4_completeness.ml`
```
g `!p. TF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [K4_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] );;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT K4_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                K4_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC );;
e (MATCH_MP_TAC TF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT K4_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                  K4_STANDARD_REL p) IN GEN_STANDARD_FRAME K4_AX p`
                 MP_TAC);;
e (ASM_MESON_TAC[K4F_IN_K4_STANDARD_FRAME; K4_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let K4_COMPLETENESS_THM = top_thm ();;
```

#### Completeness of GL in `gl_completeness.ml`

```
 g `!p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
        ==> [GL_AX . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] );;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT GL_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
               GL_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC );;
e (MATCH_MP_TAC ITF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT GL_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
                   GL_STANDARD_REL p) IN GEN_STANDARD_FRAME GL_AX p`
                  MP_TAC);;
e (ASM_MESON_TAC[GLF_IN_GL_STANDARD_FRAME; GL_STANDARD_FRAME_DEF]);;
e (ASM_MESON_TAC[GEN_COUNTERMODEL_ALT]);;
let GL_COMPLETENESS_THM = top_thm ();;
```

###  Modal completeness for models on a generic (infinite) domain.
Observe that our proof of completness ha an issue, it requires that `CORR S` is not just a set of correspondent frames but that it is a set of correspondent frames that has domain that is finite  and that is a set formulas' lists. Thanks to the parametric lemma `GEN_LEMMA_FOR_GEN_COMPLETENESS`, we quickly generalize for each normal system the completeness theorem for models with infinite worlds. <br>
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

### In T
Construction of the countermodels.
```
let T_STDWORLDS_RULES,T_STDWORLDS_INDUCT,T_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT T_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN T_STDWORLDS p`;;

let T_STDREL_RULES,T_STDREL_INDUCT,T_STDREL_CASES = new_inductive_definition
  `!w1 w2. T_STANDARD_REL p w1 w2
           ==> T_STDREL p (set_of_list w1) (set_of_list w2)`;;
```

Theorem of existence of the finite countermodel.
```
T_COUNTERMODEL_FINITE_SETS
|- `!p. ~ [T_AX . {} |~ p] ==> ~holds_in (T_STDWORLDS p, T_STDREL p) p`
```

### In K4
Construction of the countermodels.
```
let K4_STDWORLDS_RULES,K4_STDWORLDS_INDUCT,K4_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT K4_AX p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN K4_STDWORLDS p`;;

let K4_STDREL_RULES,K4_STDREL_INDUCT,K4_STDREL_CASES = new_inductive_definition
  `!w1 w2. K4_STANDARD_REL p w1 w2
           ==> K4_STDREL p (set_of_list w1) (set_of_list w2)`;;
```

Theorem of existence of the finite countermodel.
```
K4_COUNTERMODEL_FINITE_SETS
|- `!p. ~ [K4_AX . {} |~ p] ==> ~holds_in (K4_STDWORLDS p, K4_STDREL p) p`
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

Our tactic `T_TAC` and its associated rule `T_RULE` still are the naive ones, but what we did in `k_completeness.ml` and in `gl_completeness.ml` demonstrate that in future works we will automatically prove theorems in the modal logic T.


### In K4

Our tactic `K4_TAC` and its associated rule `K4_RULE` still are the naive ones, but what we did in `k_completeness.ml` and in `gl_completeness.ml` demonstrate that in future works we will automatically prove theorems in the modal logic K4.


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
