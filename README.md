# HOLMS: A HOL Light Library for Modal Systems

(c) Copyright, Antonella Bilotta, Marco Maggesi, Cosimo Perini Brogi, Leonardo Quartini 2024. <br>
(c) Copyright, Antonella Bilotta, Marco Maggesi, Cosimo Perini Brogi 2025.

See the [website](https://holms-lib.github.io/) for a brief overview of our [HOLMS library](https://github.com/HOLMS-lib/HOLMS) for the [HOL Light](https://hol-light.github.io/) theorem prover.

This repository presents a second version of HOLMS (HOL-Light Library for Modal Systems), a modular framework designed to implement modal reasoning within the HOL Light proof assistant.

Extending our [previous work on Gödel-Löb logic (GL)](https://doi.org/10.1007/s10817-023-09677-z), we generalise our approach to formalise modal adequacy proofs for axiomatic calculi, thereby enabling the coverage of a broader range of normal modal systems. If the first version of HOLMS, [presented at Overlay 2024](https://ceur-ws.org/Vol-3904/paper5.pdf), partially parametrised the completeness proof for GL and added the minimal system K, this second version of HOLMS fully generalises our method and, as a demonstration of the flexibility of our methodology, four modal system and their adequacy proofs are now implemented in HOLMS:
- **K**: the minimal system is developed in `k_completeness.ml`;
- **K4**: a system properly extended by GL is developed in `k4_completeness.ml`;
- **GL**: provability logic is developed and fully parametrised in `gl_completeness.ml`;
- **T**: a system that is not extended by GL or K4, nor is an extension of GL or K4 is developed in `t_completeness.ml`.

HOLMS lays the foundation for a comprehensive tool for modal reasoning in HOL, offering a high level of confidence and full automation by providing the essential mathematical components of principled decision algorithms for modal systems. The prototypical automated theorem prover and countermodel constructor for K, T, K4, and GL (implemented in `k_decid.ml`, `t_decid.ml`, `k4_decid.ml`, and `gl_decid.ml`, resp.) serve as evidence of the feasibility of this approach merging general purpose proof assistants, enriched sequent calculi, and formalised mathematics.

The top-level file is `make.ml`.

## Main Theorems

For each normal system $S$ implemented in HOLMS, we prove the following main theorems in its file `S_completeness.ml:
- 1. **Identification of the set of frames appropriate to $S$** <br> proves that a certain set of finite frames $C$, distinguished by a certain property of the accessibility relation, is the set of frames **appropriate** to $S$; i.e. for each frame in this set if a modal formula $p$ is a theorem of $S$, then $p$ is valid in it. <br>
$C = \mathsf{APPR}(S)$ and equivalently $\forall F \in C\ (\mathcal{S}. \varnothing \vdash p \implies F \vDash p) \ and \ \forall F\ ((\mathcal{S}. \varnothing \vdash p \implies F \vDash p) \implies F \in C)$
(`APPRS_APPR_S`)
- 2. **Soundness of $S$ with respect to $\mathsf{APPR}(S)$**  <br>
proves that if something is a theorem of $S$, then it is valid in its set of appropriate frames. <br>
$\forall p\ (\mathcal{S}. \varnothing  \vdash p \implies \mathsf{APPR}(S) \vDash p)$
(`S_APPRS_VALID`)
- 3. **Consistency of S** <br>
proves that $S$ cannot prove the false. <br>
$\mathcal{S}. \varnothing  \not \vdash \bot$
(`S_CONSISTENT`)
- 4. **Completeness of $S$ related to $\mathsf{APPR}(S)$** <br>
proves that if something holds in the set appropriate to $S$, then it is a theorem of $S$. <br>
$\forall p\ (\mathsf{APPR}(S) \vDash p \implies \mathcal{S}. \varnothing   \vdash p)$
(`S_COMPLETENESS_THM`)

For example, in `t_completeness.ml` we prove: (1) `RF_APPR_T`; (2) `T_RF_VALID`; (3) `T_CONSISTENT`; (4) `T_COMPLETENESS_THM`.

Moreover, HOLMS implements **fully automated theorem prover and countermodel constructor** for the modal logics $K, T, K4$, and $GL$: 
- `HOLMS_RULE`automatically proves theorems of these systems;
- `HOLMS_BUILD_COUNTERMODEL` outputs a countermodel if the given formula is not a theorem of the logic under analysis.


To generalise and parametrise the proofs of completeness for normal systems as much as possible, we develop four main theorems in `gen_completeness.ml`:
1. `GEN_TRUTH_LEMMA`;
2. `GEN_ACCESSIBILITY_LEMMA`;
3.  `GEN_COUNTERMODEL_ALT `;
4.  `GEN_LEMMA_FOR_GEN_COMPLETENESS`.


# Usage guide and source code

## Axiomatic Calcus
We define a ternary predicate $\mathcal{S}.\mathcal{H} \vdash p$, which denotes the derivability of a modal formula $p$ from a set of hypotheses $\mathcal{H}$ in an axiomatic extension of logic K via schemas in the set $\mathcal{S}$.

Notice that, by doing so,  we conceptualise _derivability from_ $\mathcal{H}$ _in_ $\mathcal{S}$ as _derivability from_ $\mathcal{H}$ _in a minimal axiomatic system_ K _that is extended by additional axiom schemas in_ $\mathcal{S}$.

We inductively define the **axioms** of the minimal calculus K (`K_AXIOMS`).
```
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
```
Then, we inductively introduce the **derivability relation** of our calculus (`MODPROVES`).
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
This lemma guarantees the reduction of the common notion of derivability of modal formula $p$ in an
axiomatic calculus characterised by the axiom schemata in S $\mathcal{S} \vdash p$ to the ternary relation $\mathcal{S}.\mathcal{H} \vdash p$.
```
MODPROVES_DEDUCTION_LEMMA
|- !S H p q. [S . H |~ p --> q] <=> [S . p INSERT H |~ q]
```

## Kripke's Semantics of formulae

We define, by induction on the complexity of a formula, that a certain modal formula $p$ **holds in a certain world $w$ of a certain model $\langle W, R, V\rangle$**. <br>
$w \Vdash_{\langle W, R, V\rangle} p$
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
We say that a formula $p$ **holds in a certain frame** iff it holds for every model in every world  of that frame. <br>
$\langle W, R\rangle \vDash p \iff \forall V\ (\forall w \in W\ (w \Vdash_{\langle W, R, V\rangle} p$))
```
let holds_in = new_definition
  `holds_in (W,R) p <=> !V w:W. w IN W ==> holds (W,R) V p w`;;
```
We say that a formula $p$ is **valid in a class of frames** iff it holds in every frame of this class. <br>
$L \vDash p \iff \forall \langle W,R \rangle \in L\ (\langle W,R \rangle \vDash p)$
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
We define the **set of frames appropriate to S**, i.e. the set of all the finite frames such that if p is a theorem of S, then p holds in this frame. <br>
{ $\langle W,R \rangle \in \mathtt{FINITE\textunderscore FRAMES}| \forall p\ (\mathcal{S}. \varnothing  \vdash p \implies \langle W,R \rangle \vDash p)$ }
```
let APPR_DEF = new_definition
  `APPR S = {(W:W->bool,R:W->W->bool) |
             (W,R) IN FINITE_FRAME /\
             (!p. [S. {} |~ p] ==> holds_in (W,R) p)}`;;
```
For each one of the normal system S developed in HOLMS we prove what set of frames is appropriate to S ( $C = \mathsf{APPR}(S)$ ), i.e. we prove that every frame that is in C is appropriate to S ($\subseteq$: $\forall F \in C\ (\mathcal{S}. \varnothing  \vdash p \implies F \vDash p)$ ) and that every frame that is appropriate to S is in C ($\supseteq$: $\forall F\ ((\mathcal{S}. \varnothing  \vdash p \implies F \vDash p) \implies F \in C)$  ).

### K-Finite Frames
We prove that the set of **finite frames** is the one appropriate to **$K$**.
```
FINITE_FRAME_APPR_K
|- FINITE_FRAME:(W->bool)#(W->W->bool)->bool = APPR {}
```
### T-Finite Reflexive Frames (RF)
We prove that the set of **finite reflexive frames** is the one appropriate to **$T$**.
```
let T_AX = new_definition
  `T_AX = {Box p -->  p | p IN (:form)}`;;

let RF_DEF = new_definition
 `RF =
  {(W:W->bool,R:W->W->bool) |
   ~(W = {}) /\
   (!x y:W. R x y ==> x IN W /\ y IN W) /\
   FINITE W /\
   (!x. x IN W ==> R x x)}`;;

RF_APPR_T
|- RF: (W->bool)#(W->W->bool)->bool = APPR T_AX
```
### K4-Finite Transitive Frames (TF)
We prove that the set of **finite transitive frames** is the one appropriate to **$K4$**.
```
let K4_AX = new_definition
  `K4_AX = {Box p --> Box Box p | p IN (:form)}`;;

let TF_DEF = new_definition
  `TF =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    FINITE W /\
    (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

TF_APPR_K4
|- TF: (W->bool)#(W->W->bool)->bool = APPR K4_AX
```

### GL-Finite Irreflexive and Transitive Frames (ITF)
We prove that the set of **finite transitive and irreflexive frames** is the one appropriate to **$GL$**.
```
let GL_AX = new_definition
  `GL_AX = {Box (Box p --> p) --> Box p | p IN (:form)}`;;

let ITF_DEF = new_definition
  `ITF =
   {(W:W->bool,R:W->W->bool) |
    ~(W = {}) /\
    (!x y:W. R x y ==> x IN W /\ y IN W) /\
    FINITE W /\
    (!x. x IN W ==> ~R x x) /\
    (!x y z. x IN W /\ y IN W /\ z IN W /\ R x y /\ R y z ==> R x z)}`;;

ITF_APPR_GL
|- ITF: (W->bool)#(W->W->bool)->bool = APPR GL_AX
```

## Soundness and Consistency
We parametrically demonstrate the **soundness** of each $S$ with respect to $\mathsf{APPR}(S)$.
```
GEN_APPR_VALID
|- !S p. [S. {} |~ p] ==> APPR S:(W->bool)#(W->W->bool)->bool |= p
```

Then, by specializing the proof of `GEN_APPR_VALID`, we prove the soundness of each normal system  $S$ developed in HOLMS with respect to its appropriate frame.
Moreover we prove its **consistency**, by modus ponens on the converse of `S_APPRS_VALID`.

### Soundness and consistency of K
```
let K_FINITE_FRAME_VALID = prove
 (`!p. [{} . {} |~ p] ==> FINITE_FRAME:(W->bool)#(W->W->bool)->bool |= p`,
  ASM_MESON_TAC[GEN_APPR_VALID; FINITE_FRAME_APPR_K]);;

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
  MESON_TAC[GEN_APPR_VALID; RF_APPR_T]);;

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
  MESON_TAC[GEN_APPR_VALID; TF_APPR_K4]);;

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
ASM_MESON_TAC[GEN_APPR_VALID; ITF_APPR_GL]);;

let GL_consistent = prove
 (`~ [GL_AX . {} |~  False]`,
  REFUTE_THEN (MP_TAC o MATCH_MP (INST_TYPE [`:num`,`:W`] GL_ITF_VALID)) THEN
  REWRITE_TAC[valid; holds; holds_in; FORALL_PAIR_THM;
              IN_ITF; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`{0}`; `\x:num y:num. F`] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; FINITE_SING; IN_SING] THEN MESON_TAC[]);;
```

## Completeness Theorems
We first sketch the idea behind the demonstration and, then, we will present a three-step proof.

### The Idea behind the Proof

Given a modal system $S$, we want to prove that it is **complete with respect to the set of its appropriate frames**: $\forall p (\mathsf{APPR}(S) \vDash p \implies \mathcal{S}. \varnothing  \vdash p)$

```
val it : goalstack = 1 subgoal (1 total)
`!p. APPR S |= p ==> [S. {} |~ p]`
```
- **1. Rewriting `S_COMPLETENESS`'s statement** <br>
By using some tautologies and rewritings, we can show that the completeness theorem is equivalent to a more handy sentence:  <br>
$\forall p (\mathcal{S}. \varnothing  \not \vdash p \implies \exists \langle W,R\rangle_{S,p} \in \mathsf{APPR}(S) (\exists V_{S,p} \exists m_{S,p} \in W_{S,p} (\langle W_{S,p}, R_{S,p}, V_{S,p} \rangle, m_{S,p} \not \vDash p))$ <br> <br>
  - A. We rewrote the sentence by _contraposition_. <br>
   `e GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM];;` <br> <br>
  - B. We rewrote validity in a set of frames (`valid`) as validity in a certain world of a certain model (`holds`) and we exploited some _propositional tautologies_. <br>
   `e (REWRITE_TAC[valid; NOT_FORALL_THM; FORALL_PAIR_THM; holds_in; NOT_IMP]);;` <br>
```
val it : goalstack = 1 subgoal (1 total)
`!p. ~[S . {} |~ p]
     ==> ?W R. (W,R) IN APPR S /\
               (?V m. m IN W /\ ~holds (W,R) V p w)`
```
To prove this rewritten statement, we need to construct a **_countermodel_** $𝓜_{S,p}$ and a "**_counterworld_**" $m_{S,p}$ in the domain of the countermodel for each modal formula $p$. <br> <br>
We can observe that, by working with HOL, we identify all those lines of reasoning that are **_parametric_** with respect to $S$ (the axiom system) and to  $p$ (the formula we are analysing) and we develop the completeness proof while **avoiding code duplication as much as possible**. <br>
<br>
- **2. Reducing a model-theoretic notion to a list-theoretic concept** <br>
The canonical proof of completeness, illustrated in classical textbooks like [George Boolos's "The Logic of Provability"](https://www.cambridge.org/core/books/logic-of-provability/F1549530F91505462083CE2FEB6444AA), exploits the idea of working in a context (_countermodel_) such that: $\forall w \in W_{S,p} (w \in p \iff 𝓜_{S,p},w \vDash p) $. <br> <br>
Observe that, in such a context, the members of the domain $W_{S,p}$ are lists of modal formulas.
If we are able to construct a countermodel with these constraints, we will easily construct a counterworld $m_{S,p}$ that is a list of formulas not including p.
<br> <br>
Then our subgoal would be to prove: <br>
```
val it : goalstack = 1 subgoal (1 total)
`!p. ~[S . {} |~ p]
       ==> ?W R. (W,R) IN APPR S /\
                 (?M. M IN W /\ ~ MEM p M)`
```
This subgoal is much more manageable than the previous one, indeed it reduces the **model-theoretic** notion of _validity_ (`holds (W,R) V p w`) to the **list-theoretic** concept of _membership_ (`MEM p w`).

- **3. What do we need to prove?** <br>
Given our aim of proving $\forall p(\mathcal{S}. \varnothing  \not \vdash p \implies \exists \langle W,R \rangle_{S,p} \in \mathsf{APPR}(S) (\exists m_{S,p} \in W_{S,p}(p \not \in m_{S,p})))$, we need a countermodel and counterworld following these constraints: <br> <br>
  - A. The Kripke's frame $\langle W,R \rangle_{S,p}$ must be **appropriate** to S. <br>
    $\langle W,R \rangle_{S,p} \in \mathsf{APPR}(S)$ <br> <br>
  - B. The Kripke's model $𝓜_{S,p} = \langle W,R,V \rangle_{S,p}$ must allow us to **reduce validity to membership** for every subformula of p. <br>
    Namely, for our model $𝓜_{S,p}$ holds
    $\forall q (q < p \ \implies \ \forall w \in W_{S,p} (w \in q \iff 𝓜_{S,p},w \vDash q))$,
    where $<$ denotes the subformula relation. <br>
  - C. The counterworld $m_{S,p}$ must not contain $p$.<br>
  - D. $W_{S,p}$ must be a **set of formulas lists** <br>
    `APPR S:(form list->bool)#(form list->form list->bool)->bool`.

### STEP 1: Partial definition of a parametric Standard Model

We partially identify the countermodel $𝓜_{S,p} = \langle W,R,V \rangle_{S,p}$ by defining $W_{S,p}$ as a set of maximal consistent lists, $V$ as a particular binary relation over formulas' atoms and worlds and by requesting two constraints for $R_{S,p}$. The definition of `S_STANDARD_MODEL` in step 1 is fully parametric and does not involve any peculiarities of the modal system $S$. Consequently this definition is pesented in `gen_completeness.ml` as `GEN_STANDARD_MODEL`.

### Consistency and Maximal Consistency
Before we build up the countermodel, we define in `consistent.ml` some properties that hold for formulas lists and that will be useful to define the domain of the countermodel.

#### S-Consistent 
A list of formulas $X$ is $S$-consistent to a set of axioms $S$ iff and only if $\mathcal{S.} \varnothing  \not \vdash \neg \bigwedge X$
```
let CONSISTENT = new_definition
  `CONSISTENT S (X:form list) <=> ~[S . {} |~ Not (CONJLIST X)]`;;
```

#### S,p-Maximal Consistent  <br>
A list of formulas $X$ is $(S,p)$-maximal to a set of axioms $S$ and modal formula $p$ iff $X \ \text{has no repetitions}$, $X \ is \ S\text{-consistent}$ and $\forall q (q < p \implies q \in X \lor \neg q \in l)$.
```
let MAXIMAL_CONSISTENT = new_definition
  `MAXIMAL_CONSISTENT S p X <=>
   CONSISTENT S X /\ NOREPETITION X /\
   (!q. q SUBFORMULA p ==> MEM q X \/ MEM (Not q) X)`;;
```

#### Extension of Consistent Lists to Maximal Consistent Lists 
**Lindenbaum Lemma:** $X \text{ is } S\text{-consistent} \land \forall q ( q \in X \implies (q < p \lor \neg q < p)) \implies \exists M (X \subseteq M \ \land \ M \text{ is } (S,p)\text{-maximal-consistent} )$
```
EXTEND_MAXIMAL_CONSISTENT
|- !S p X. CONSISTENT S X /\
           (!q. MEM q X ==> q SUBSENTENCE p)
           ==> ?M. MAXIMAL_CONSISTENT S p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p) /\
                   X SUBLIST M
```

### Definition of the parametric Countermodel
We define a **standard model** such that:

- **A: The Domain $W_{S,p}$  is { $X | (S,p)\text{-maximal-consistent} \ X \land \forall q ( q \in X \implies (q < p \lor \neg q < p))$ }** <br> <br>
As requested, the domain is a set of lists of formulas and, in particular, it is a **subclass of maximal consistent sets of formulas**. <br>
  Observe that, in principle, we can employ general **sets** of formulas in the formalisation. However, from the practical viewpoint, **lists without repetitions** are better suited in HOL since they are automatically finite and we can easily manipulate them by structural recursion. <br> <br>
We prove, as requested for the domain of a frame, that $W_{S,p}$ is **non-empty** by using `NONEMPTY_MAXIMAL_CONSISTENT`, a corollary of the lemma of extension of maximal consistent lists.
```
NONEMPTY_MAXIMAL_CONSISTENT
|- !S p. ~ [S . {} |~ p]
         ==> ?M. MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)
```

- **B: The Accessibility Relation $R_{S,p}$** should meet two conditions
   - R1: $\forall q \in Form_{\Box} (\Box q < p \implies \forall w \in W_{S,p}(\Box q \in w \Leftrightarrow \forall x (wRx \implies q \in x)))$. <br>
     This condition ensures that our list-theoretic translation follows Kripke's semantics.
   - R2: $\langle W,R \rangle_{S,p} \in \mathsf{APPR}(S)$. <br>
    This second condition guarantees one of the four initial constraints.

- **C: The Evaluation Relation $V_{S,p}$** is defined as follows <br>
  $\forall m \in W_{S,p} \ \forall a \in \text{Atom-Form}_{\Box} (mVa \iff a < p \land a \in m)$

In particular, in HOLMS's `gen_completeness.ml` we develop a parametric (to $S$ and $p$) definition  of `GEN_STANDARD_FRAME` and `GEN_STANDARD_MODEL` and then we specialize these definitions for each normal system.

```
let GEN_STANDARD_FRAME_DEF = new_definition
  `GEN_STANDARD_FRAME S p =
   APPR S INTER
   {(W,R) | W = {w | MAXIMAL_CONSISTENT S p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
            (!q w. Box q SUBFORMULA p /\ w IN W
                   ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))}`;;

let GEN_STANDARD_MODEL_DEF = new_definition
  `GEN_STANDARD_MODEL S p (W,R) V <=>
   (W,R) IN GEN_STANDARD_FRAME S p /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;
```
Because the definitions of `K_STANDARD_MODEL`, `T_STANDARD_MODEL`, `K4_STANDARD_MODEL` and `GL_STANDARD_MODEL` are just instances of `GEN_STANDARD_FRAME` and `GEN_STANDARD_MODEL` with the parameters `{}`, `T_AX`, `K4_AX` and `GL_AX`, here we present only the definitions for $K4$.

Definitions in `k4_completeness.ml` (`S`=`K4_AX`)
```
let K4_STANDARD_FRAME_DEF = new_definition
`K4_STANDARD_FRAME p = GEN_STANDARD_FRAME K4_AX p`;;

IN_K4_STANDARD_FRAME
|- !p W R. (W,R) IN K4_STANDARD_FRAME p <=>
           W = {w | MAXIMAL_CONSISTENT K4_AX p w /\
                    (!q. MEM q w ==> q SUBSENTENCE p)} /\
           (W,R) IN TF /\
           (!q w. Box q SUBFORMULA p /\ w IN W
                  ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))

let K4_STANDARD_MODEL_DEF = new_definition
   `K4_STANDARD_MODEL = GEN_STANDARD_MODEL K4_AX`;;

K4_STANDARD_MODEL_CAR
|- !W R p V.
     K4_STANDARD_MODEL p (W,R) V <=>
     (W,R) IN K4_STANDARD_FRAME p /\
     (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))
```

### STEP 2: Definition of a standard accessibility relation for each S
The definition of a _standard acessibility relation_ cannot be fully parametrised, at least following the approach presented in classical textbook.

Consequently, to avoid code repetition, we will:

- A: Define a parametric `GEN_STANDARD_REL` in `gen_completeness.ml`,
- B: Complete the definition of `S_STANDARD_REL` in its spefic file `S_completeness.ml`, in a way that guarantees the conditions R1 and R2.
  In particular, we will show:
  - The most difficult verse of R1's implication in `S_ACCESSIBILITY_LEMMA` <br>
$\forall q \in Form_{\Box} (\Box q < p \implies \forall w \in W_{S,p}(\Box q \in w \Longleftarrow \forall x (wRx \implies q \in x)))$
  - R2 holds for $\langle W_{S,p},$ _S_STANDARD_REL_ $\rangle$ in `S_MAXIMAL_CONSISTENT`. <br>
    $\langle W_{S,p},$ _S_STANDARD_REL_ $\rangle  \in \mathsf{APPR}(S)$
  Then `SF_IN_STANDARD_S_FRAMEE` follows as corollary and, given the hypotesis $\mathcal{S}.\varnothing  \not \vdash p$,  $\langle W_{S,p},$ S_STANDARD_REL $, V_{S,p} \rangle$ is an `S_STANDARD_MODEL`.

#### A: Parametric definition of the standard relation in `gen_completeness`.
```
let GEN_STANDARD_REL = new_definition
  `GEN_STANDARD_REL S p w x <=>
   MAXIMAL_CONSISTENT S p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT S p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)`;;
```

#### B.K: Definition of the standard relation for K in `k_completeness.ml`.
```
let K_STANDARD_REL_DEF = new_definition
  `K_STANDARD_REL p = GEN_STANDARD_REL {} p`;;

K_STANDARD_REL_CAR
|- K_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT {} p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT {} p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM B x)
```

**Accessibility lemma for K** that ensures the most difficult verse of R1's implication.
```
K_ACCESSIBILITY_LEMMA
|- !p w q. ~ [{} . {} |~ p] /\
     MAXIMAL_CONSISTENT {} p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. K_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`
```
**Maximal consistent lemma for K** ensures R2.
```
K_MAXIMAL_CONSISTENT
|- !p. ~ [{} . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT {} p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            K_STANDARD_REL p)
           IN FINITE_FRAME`,
```
Proof of the corollary that ensures that **our construction for K is a standard frame**.
```
g `!p. ~ [{} . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT {} p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
            K_STANDARD_REL p)
           IN K_STANDARD_FRAME p`;;
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

#### B.T: Definition of the standard relation for T in `t_completeness.ml`.
```
let T_STANDARD_REL_DEF = new_definition
  `T_STANDARD_REL p w x <=>
   GEN_STANDARD_REL T_AX p w x`;;

T_STANDARD_REL_CAR
|- !p w x.
     T_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT T_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT T_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM B x)
```

**Accessibility lemma for T** that ensures the most difficult verse of R1's implication.
```
T_ACCESSIBILITY_LEMMA
|- !p w q.
     ~ [T_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT T_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. T_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w
```
**Maximal consistent lemma for T** that ensures R2.
```
RF_MAXIMAL_CONSISTENT
|- !p. ~ [T_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT T_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            T_STANDARD_REL p)
           IN RF `
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
#### B:K4: Definition of the standard relation for K4 in `k4_completeness.ml`.
```
let K4_STANDARD_REL_DEF = new_definition
  `K4_STANDARD_REL p w x <=>
   GEN_STANDARD_REL K4_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x)`;;

K4_STANDARD_REL_CAR
|- !p w x.
     K4_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT K4_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT K4_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM (Box B) x /\ MEM B x)
```

**Accessibility lemma for K4** that ensures the most difficult verse of R1's implication.
```
K4_ACCESSIBILITY_LEMMA
|- !p w q.
     ~ [K4_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT K4_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. K4_STANDARD_REL p w x ==> MEM q x)
          ==> MEM (Box q) w
```
**Maximal consistent lemma for K4** that ensures R2.
```
TF_MAXIMAL_CONSISTENT
|- !p. ~ [K4_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT K4_AX p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)},
            K4_STANDARD_REL p)
           IN TF `
```
Proof of the corollary that ensures that **our construction for K4 is a standard frame**.
```
g `!p. ~ [K4_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT K4_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
             K4_STANDARD_REL p) IN K4_STANDARD_FRAME p`;;
e (INTRO_TAC "!p; not_theor_p");;
e (REWRITE_TAC[IN_K4_STANDARD_FRAME]);;
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

#### B.GL: Definition of the standard relation for GL in `gl_completeness.ml`.
```
let GL_STANDARD_REL_DEF = new_definition
  `GL_STANDARD_REL p w x <=>
   GEN_STANDARD_REL GL_AX p w x /\
   (!B. MEM (Box B) w ==> MEM (Box B) x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

GL_STANDARD_REL_CAR
|- !p w x.
     GL_STANDARD_REL p w x <=>
     MAXIMAL_CONSISTENT GL_AX p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT GL_AX p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
     (!B. MEM (Box B) w ==> MEM (Box B) x /\ MEM B x) /\
     (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)
```

**Accessibility Lemma for GL** that ensures the most difficult verse of R1's implication.
```
GL_ACCESSIBILITY_LEMMA
|- !p w q.
     ~ [GL_AX . {} |~ p] /\
     MAXIMAL_CONSISTENT GL_AX p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w
```
**Maximal Consistent Lemma for GL** that ensures R2.
```
ITF_MAXIMAL_CONSISTENT
|- !p. ~ [GL_AX . {} |~ p]
         ==> ({M | MAXIMAL_CONSISTENT GL_AX p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p)},
              GL_STANDARD_REL p)
             IN ITF
```
Proof of the corollary that ensures that **our construction for GL is a standard frame**.
```
g `!p. ~ [GL_AX . {} |~ p]
       ==> ({M | MAXIMAL_CONSISTENT GL_AX p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
            GL_STANDARD_REL p)
           IN GL_STANDARD_FRAME p`;;
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
In this step, we prove that, given a standard model and $\mathcal{S}. \varnothing  \not \vdash p$, the _desiderandum_ in the proof sketch holds, and indeed something stronger holds:
_For every subformula q of p_ we can reduce the notion of `holds (W,R) V q w` to the list-theoretic one of membership `MEM q w`.

Observe that we prove this foundamental lemma in a fully parametric way and, moreover, the proof of completeness does not need to specify this lemma for the normal system in analysis.

#### Parametric truth lemma in `gen_completeness.ml` (parameters P, S)
```
GEN_TRUTH_LEMMA
|- !S W R p V q.
     ~ [S . {} |~ p] /\
     GEN_STANDARD_MODEL S p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)
```

### The Theorems

We built up a _countermodel_ $\langle W,R,V \rangle_{S,p}$ that is a _standard model for S_, and now we want to prove that a _counterworld_ in this model exists:  $\exists m_{S,p} \in W_{S,p} (p \not \in m_{S,p} )$. So we need an $m_{S,p}$ such that:
 - A: $m_{S,p} \in W_{S,p}$ that is to say $m_{S,p}$ is $(S,p)\text{-maximal-consistent}$;
 - B: $p \not \in m_{S,p}$

Thanks to our theorem `NONEMPTY_MAXIMAL_CONSISTENT` $\forall p (\mathcal{S}.\varnothing  \vdash p \implies (\exists m (\m \text{ is }(S,p)\text{-maximal-consistent} \ \land \ \neg p \in M))$, we know that such an $m_{S,p}$ exists and we can prove `GEN_COUNTERMODEL_ALT`. Observe, indeed, that $m$ is $(S,p)$--maximal-consistent $\land \ \neg p \in m_{S,p} \implies p \not \in m_{S,p}$.
```
NONEMPTY_MAXIMAL_CONSISTENT
|- !S p. ~ [S . {} |~ p]
         ==> ?M. MAXIMAL_CONSISTENT S p M /\
                 MEM (Not p) M /\
                 (!q. MEM q M ==> q SUBSENTENCE p)

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

Given the fully parametrised `GEN_COUNTERMODEL_ALT` and `SF_IN_STANDARD_S_FRAME`, the completeness theorems for every $S$ follow and their proofs are so brief that we can present them here.

#### Completeness of K in `k_completeness.ml`.
```
g `!p. FINITE_FRAME:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> [{} . {} |~ p]`;;
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] );;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT {} p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                K_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC );;
e (MATCH_MP_TAC K_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT {} p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
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
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT T_AX p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                T_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
 e (MATCH_MP_TAC RF_MAXIMAL_CONSISTENT);;
 e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT T_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
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
e (GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM]);;
e (INTRO_TAC "p_not_theor");;
e (REWRITE_TAC[valid; NOT_FORALL_THM]);;
e (EXISTS_TAC `({M | MAXIMAL_CONSISTENT K4_AX p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                K4_STANDARD_REL p)`);;
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
e (MATCH_MP_TAC TF_MAXIMAL_CONSISTENT);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `({M | MAXIMAL_CONSISTENT K4_AX p M /\
                       (!q. MEM q M ==> q SUBSENTENCE p)},
                  K4_STANDARD_REL p)
                 IN GEN_STANDARD_FRAME K4_AX p`
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
e (REWRITE_TAC[NOT_IMP] THEN CONJ_TAC);;
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
Observe that our proof of completeness requires that `APPR S` is not just a set of appropriate frames (`APPR S:(W->bool)#(W->W->bool)->bool`) but a set of appropriate frames sitting on the type of **formulas' lists** (`APPR S:(form list->bool)#(form list->form list->bool)->bool`). Nevertheless, thanks to the parametric lemma `GEN_LEMMA_FOR_GEN_COMPLETENESS`, we can quickly generalise each completeness theorem for models on domains with a  generic infinite type.


In `gen_completeness.ml`.
```
GEN_LEMMA_FOR_GEN_COMPLETENESS
|- !S. INFINITE (:A)
       ==> !p. APPR S:(A->bool)#(A->A->bool)->bool |= p
               ==> APPR S:(form list->bool)#(form list->form list->bool)->bool |= p
```
As corollaries of `GEN_LEMMA_FOR_GEN_COMPLETENESS`, in the specific files.
```
K_COMPLETENESS_THM_GEN
|- !p. INFINITE (:A) /\ FINITE_FRAME:(A->bool)#(A->A->bool)->bool |= p
       ==> [{} . {} |~ p]

T_COMPLETENESS_THM_GEN
|- !p. INFINITE (:A) /\ RF:(A->bool)#(A->A->bool)->bool |= p
       ==> [T_AX . {} |~ p]

K4_COMPLETENESS_THM_GEN
|- !p. INFINITE (:A) /\ TF:(A->bool)#(A->A->bool)->bool |= p
       ==> [K4_AX . {} |~ p]

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
|- !p. ~ [T_AX . {} |~ p] ==> ~holds_in (T_STDWORLDS p, T_STDREL p) p
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
|- !p. ~ [K4_AX . {} |~ p] ==> ~holds_in (K4_STDWORLDS p, K4_STDREL p) p
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

Our tactic `HOLMS_TAC` and its associated rule `HOLMS_RULE` can automatically prove theorems in the modal logics K, T, K4 and GL by performing a root-first proof search in the associated labelled sequent calculus.
When the tactic halts witout reaching a proof, the proof state holds a countermodel.  The procedure `HOLMS_BUILD_COUNTERMODEL` outputs the generated countermodel.

Here we report two basic examples.
More examples of proofs and countermodels can be found in the file `tests.ml`.

### Example of automatic theorem syntesis

Automatic proof of the Formal Second Incompleteness Theorem in the Gödel–Löb modal logic:
```
# HOLMS_RULE `[GL_AX . {} |~ Not Box False --> Not Box Diam True]`;;
```

### Example of countermodel generation

Generation of a countermodel to the Löb schema in the modal logic K:
```
# HOLMS_BUILD_COUNTERMODEL `[{} . {} |~ Box (Box a --> a) --> Box a]`;;
Countermodel found:
R y y' /\
y' IN W /\
R w y /\
y IN W /\
holds (W,R) V (Box (Box a --> a)) w /\
w IN W /\
~holds (W,R) V a y /\
~holds (W,R) V a y'
```
