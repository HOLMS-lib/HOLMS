# Correspondence for individual modal axiom schemata

This chapter characterizes validity of D, T, 4, B, 5, Löb's axiom, and
Grzegorczyk's axiom by properties of Kripke accessibility. It also develops
the weak well-foundedness principles needed for the last correspondence.
Each result has a mathematical statement and an informal proof, independent
of proof-assistant syntax.

The prerequisites are [modal syntax and semantics](Modal.md). The
[calculus chapter](Calculus.md) explains how axiom schemata determine modal
systems, and [ParametricCorrespondence](ParametricCorrespondence.md) connects
axiom sets with characteristic frame classes and soundness. See also the
[documentation index](README.md).

The formal developments are
[HOL Light's `ad_hoc_correspondence.ml`](../ad_hoc_correspondence.ml) and
[Lean's `HOLMS/AdHocCorrespondence.lean`](../lean/HOLMS/AdHocCorrespondence.lean).
Unless distinguished explicitly, names in **Formalization references** occur
in both files; Lean names are relative to namespace `HOLMS`.
Implementation choices are discussed in the
[AdHocCorrespondence translation notes](../lean/translation/AdHocCorrespondence.md).

## 1. Semantic conventions and axiom schemata

Let $F=(W,R)$ be a frame over an ambient domain $D$, with $W\subseteq D$
and $R\subseteq D\times D$. Satisfaction is written $F,V,w\models p$.
In particular,

$$
F,V,w\models\Box p\iff
\forall v\in W,\ R(w,v)\Longrightarrow F,V,v\models p,
$$

$$
F,V,w\models\Diamond p\iff
\exists v\in W,\ R(w,v)\land F,V,v\models p.
$$

The second clause follows classically from $\Diamond p=\neg\Box\neg p$.
Frame validity $F\models p$ quantifies over every valuation $V$ and every
$w\in W$. A schema is valid when **every formula instance** is valid.

The seven schemata considered here are:

| Schema | Instance at $p$ | HOL Light definition | Lean definition |
|---|---|---|---|
| D | $\Box p\to\Diamond p$ | `D_SCHEMA_DEF` | `D_SCHEMA` |
| T | $\Box p\to p$ | `T_SCHEMA_DEF` | `T_SCHEMA` |
| 4 | $\Box p\to\Box\Box p$ | `FOUR_SCHEMA_DEF` | `FOUR_SCHEMA` |
| B | $p\to\Box\Diamond p$ | `B_SCHEMA_DEF` | `B_SCHEMA` |
| 5 | $\Diamond p\to\Box\Diamond p$ | `FIVE_SCHEMA_DEF` | `FIVE_SCHEMA` |
| Löb | $\Box(\Box p\to p)\to\Box p$ | `LOB_SCHEMA_DEF` | `LOB_SCHEMA` |
| Grzegorczyk | $\Box(\Box(p\to\Box p)\to p)\to p$ | `GRZ_SCHEMA_DEF` | `GRZ_SCHEMA` |

The table refers to the [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean) sources; the HOL Light
constants themselves have the names in the last column. We write these
schemata mathematically as $\mathrm D(p)$, $\mathrm T(p)$, $\mathrm{4}(p)$,
$\mathrm B(p)$, $\mathrm{5}(p)$, $\mathrm{L\ddot ob}(p)$, and
$\mathrm{Grz}(p)$.

A recurring device in the converse proofs is to choose an atom $a$ whose
truth set is a prescribed subset $U\subseteq D$. Valuations are unrestricted,
so setting $V(a,u)$ to mean $u\in U$ realizes that predicate. Validity of
all instances includes this atomic instance and every such valuation.
This is the formula-interpretation principle explained in [Modal](Modal.md).

## 2. Properties of accessibility

The following properties are restricted to the designated worlds:

| Property | Mathematical definition | Name in both sources |
|---|---|---|
| Seriality | $\forall x\in W,\ \exists y\in W,\ R(x,y)$ | `SERIAL` |
| Reflexivity | $\forall x\in W,\ R(x,x)$ | `REFLEXIVE` |
| Irreflexivity | $\forall x\in W,\ \neg R(x,x)$ | `IRREFLEXIVE` |
| Transitivity | $\forall x,y,z\in W,\ R(x,y)\land R(y,z)\Rightarrow R(x,z)$ | `TRANSITIVE` |
| Symmetry | $\forall x,y\in W,\ R(x,y)\Rightarrow R(y,x)$ | `SYMMETRIC` |
| Antisymmetry | $\forall x,y\in W,\ R(x,y)\land R(y,x)\Rightarrow x=y$ | `ANTISYMMETRIC` |
| Euclideanity | $\forall x,y,z\in W,\ R(x,y)\land R(x,z)\Rightarrow R(z,y)$ | `EUCLIDEAN` |

**Formalization references.** These are definitions in
[HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean), with the names listed above.

The orientation $R(z,y)$ in Euclideanity follows both sources. Exchanging
$y,z$ also gives $R(y,z)$. Antisymmetry permits self-loops and is distinct
from irreflexivity.

For the Löb and Grzegorczyk correspondences we additionally assume **edge
closure**:

$$
\forall x,y\in D,\ R(x,y)\Longrightarrow(x\in W\land y\in W).
\tag{C}
$$

The five elementary correspondences do not need (C). None of the seven
correspondence statements requires $W$ to be nonempty. This differs from
membership in the well-formed frame class defined in
[ParametricCorrespondence](ParametricCorrespondence.md), which requires both
(C) and nonemptiness.

## 3. Weak well-foundedness

### 3.1 Relation fields and removal of the diagonal

For an arbitrary relation $Q\subseteq D\times D$, define its **field** by

$$
\operatorname{fld}(Q)=\{x\in D:\exists y\in D,\ Q(x,y)\lor Q(y,x)\}.
$$

Define the relation with its diagonal removed by

$$
Q^{\ne}(y,x)\iff y\ne x\land Q(y,x).
$$

Here a $Q$-predecessor of $x$ is a point $y$ with $Q(y,x)$. Removing the
diagonal is sometimes called taking the strict part in these sources; it
does **not** mean replacing $Q(y,x)$ by $Q(y,x)\land\neg Q(x,y)$.
Distinct points related in both directions remain related in $Q^{\ne}$.

Ordinary well-foundedness $\operatorname{WF}(Q)$ means that every nonempty
subset of $D$ has a point with no $Q$-predecessor in that subset. Define
**weak well-foundedness** by

$$
\operatorname{WWF}(Q)\iff
\forall X\subseteq\operatorname{fld}(Q),\quad
X\ne\varnothing\Longrightarrow
\exists x\in X,\ \forall y\in X,\ Q(y,x)\Longrightarrow y=x.
$$

Thus weak minimality ignores self-loops but excludes distinct predecessors
inside the chosen subset.

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml):
`WWF`, using the library relation field `fld`.
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `relField`, `WWF`.
The definitions use predicates in place of the subsets written here.

### 3.2 Equivalence with ordinary well-foundedness off the diagonal

**Statement.** For every relation $Q$,

$$
\operatorname{WWF}(Q)\iff\operatorname{WF}(Q^{\ne}).
$$

**Comment.** The field restriction loses no information: points outside the
field have no predecessors at all. The result allows ordinary well-founded
induction to be used while retaining self-loops in the original relation.

**Proof.** Suppose $\operatorname{WWF}(Q)$ and take a nonempty set
$X\subseteq D$. If $X\subseteq\operatorname{fld}(Q)$, weak minimality
supplies a point with no distinct $Q$-predecessor in $X$, exactly a
$Q^{\ne}$-minimal point. Otherwise choose $x\in X$ outside the field.
No $Q(y,x)$ can hold, since it would place $x$ in the field; hence $x$ is
also $Q^{\ne}$-minimal. This proves ordinary well-foundedness.
Conversely, apply ordinary well-foundedness of $Q^{\ne}$ to each nonempty
$X\subseteq\operatorname{fld}(Q)$. Its minimal point has precisely the
property required by weak well-foundedness. $\square$

**Formalization references.**
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `wwf_iff_wellFounded_strict`.
There is no separately named counterpart in
[HOL Light](../ad_hoc_correspondence.ml).

### 3.3 Minimal-element characterization

**Statement.** For every relation $Q$,

$$
\operatorname{WWF}(Q)\iff
\forall X\subseteq\operatorname{fld}(Q),\quad
\left(X\ne\varnothing\ \Longleftrightarrow\
\exists x\in X,\ \forall y\in X,\ Q(y,x)\Longrightarrow y=x\right).
$$

**Proof.** Weak well-foundedness gives a weakly minimal element from
nonemptiness. Conversely, the existence of such an element already implies
nonemptiness. The forward direction of each displayed inner equivalence is
exactly the defining requirement for $\operatorname{WWF}(Q)$. $\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `WWF_EQ`.

### 3.4 Induction on distinct predecessors

**Statement.** For every relation $Q$, $\operatorname{WWF}(Q)$ is equivalent
to the following induction principle: for every predicate $P$ on $D$,

$$
\left(\forall x\in D,\ \neg P(x)\Longrightarrow x\in\operatorname{fld}(Q)\right)
\quad\land\quad
\left(\forall x\in D,\
  \bigl(\forall y\in D,\ Q(y,x)\land y\ne x\Longrightarrow P(y)\bigr)
  \Longrightarrow P(x)\right)
\quad\Longrightarrow\quad\forall x\in D,\ P(x).
$$

**Comment.** To establish $P(x)$, one may assume $P$ at all distinct
predecessors. The displayed side condition says that any counterexamples
lie in the field; it is retained in the formal statements.

**Proof.** Suppose weak well-foundedness holds. If $P$ has a counterexample,
the set $X=\{x:\neg P(x)\}$ is nonempty and lies in the field. Choose a
weakly minimal counterexample $x$. Every distinct predecessor satisfies $P$,
so the induction step gives $P(x)$, a contradiction.

Conversely, assume the induction principle and suppose a nonempty
$X\subseteq\operatorname{fld}(Q)$ has no weakly minimal member. Every
$x\in X$ then has a distinct predecessor $y\in X$. Apply induction to
$P(x)\iff x\notin X$. Its counterexamples lie in the field. For the
induction step, if $x\in X$, the chosen predecessor contradicts the
inductive assumptions; hence $x\notin X$. Induction would make $X$ empty,
a contradiction. Thus every such $X$ has a weakly minimal member.
$\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `WWF_IND`. Lean proves the
forward direction using the bridge of Section 3.2; the minimal-counterexample
argument above explains the same induction principle directly.

### 3.5 Orientation for accessibility

For accessibility $R$, write

$$
R^{-1}(y,x)\iff R(x,y).
$$

A predecessor for $R^{-1}$ is therefore an **accessible successor** for $R$.
Ordinary well-foundedness of $R^{-1}$ supplies an $R$-terminal member in
every nonempty subset: no successor in that subset, including itself.
Weak well-foundedness of $R^{-1}$ supplies a member with no **distinct**
successor in the subset. Self-loops are allowed in the latter case.

In the classical setting with dependent choice used by these developments,
failure of well-foundedness yields an infinite predecessor chain. Applied
to $R^{-1}$ this is a sequence $x_0Rx_1Rx_2R\cdots$; applied to
$(R^{-1})^{\ne}$ it also satisfies $x_{n+1}\ne x_n$. These observations
fix the direction of the inductions and chains used below.

This is background about well-founded relations, not a separately named
correspondence theorem. HOL Light uses the library `WF` and, in the
Grzegorczyk proof, [`DEPENDENT_CHOICE`](../dep_choice.ml); Lean uses
`WellFounded` and its library characterization by descending chains.

## 4. Elementary correspondences

Each theorem below holds for any $F=(W,R)$, without (C). In the converse
proofs, choosing a truth set for an atom is legitimate by Section 1.

### 4.1 D characterizes seriality

**Statement.**

$$
\operatorname{Serial}(W,R)\iff\forall p,\ F\models\Box p\to\Diamond p.
$$

**Comment.** Necessity implies possibility precisely when a designated world
cannot have no designated accessible successors.

**Proof.** Suppose the relation is serial on $W$. If $\Box p$ holds at
$w\in W$, choose $v\in W$ with $R(w,v)$. Then $p$ holds at $v$, witnessing
$\Diamond p$ at $w$.
Conversely, assume all D instances are valid and fix $w\in W$. Make an atom
$a$ true exactly at points $u$ with $R(w,u)$. Every designated successor of
$w$ satisfies $a$, so $\Box a$ holds at $w$. Validity of D gives
$\Diamond a$, and its witness is a designated successor of $w$. $\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `MODAL_SER`.

### 4.2 T characterizes reflexivity

**Statement.**

$$
\operatorname{Reflexive}(W,R)\iff\forall p,\ F\models\Box p\to p.
$$

**Proof.** If $w\in W$ and $R(w,w)$, the truth of $\Box p$ at $w$ implies
$p$ there by taking $w$ itself as successor. Conversely, fix $w\in W$ and
make $a$ true exactly at the $R$-successors of $w$. Then $\Box a$ holds at
$w$. Validity of T gives $a$ at $w$, which by the chosen valuation means
$R(w,w)$. $\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `MODAL_REFL`.

### 4.3 4 characterizes transitivity

**Statement.**

$$
\operatorname{Transitive}(W,R)\iff
\forall p,\ F\models\Box p\to\Box\Box p.
$$

**Comment.** Under transitivity, truth at all immediate successors extends
to truth at successors reached in two steps.

**Proof.** Suppose $\Box p$ holds at $w\in W$. Given $y,z\in W$ with
$R(w,y)$ and $R(y,z)$, transitivity gives $R(w,z)$, so $p$ holds at $z$.
Thus $\Box p$ holds at each such $y$, proving $\Box\Box p$ at $w$.
Conversely, fix $w,y,z\in W$ with those two edges and make $a$ true exactly
at the successors of $w$. Then $\Box a$ holds at $w$, and validity of 4
gives $\Box\Box a$ there. Following the two given edges gives $a$ at $z$,
which means $R(w,z)$. $\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `MODAL_TRANS`.

### 4.4 B characterizes symmetry

**Statement.**

$$
\operatorname{Symmetric}(W,R)\iff
\forall p,\ F\models p\to\Box\Diamond p.
$$

**Proof.** Suppose $p$ holds at $w\in W$. For each designated successor
$y$ of $w$, symmetry gives $R(y,w)$, so $w$ witnesses $\Diamond p$ at $y$.
Hence $\Box\Diamond p$ holds at $w$.
Conversely, take $w,y\in W$ with $R(w,y)$ and make $a$ true only at $w$.
The B instance at $w$ gives $\Diamond a$ at $y$. Its witnessing world must
be $w$, so $R(y,w)$. $\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `MODAL_SYM`.

### 4.5 5 characterizes Euclideanity

**Statement.**

$$
\operatorname{Euclidean}(W,R)\iff
\forall p,\ F\models\Diamond p\to\Box\Diamond p.
$$

**Comment.** A possible witness at one successor remains accessible from
every other successor of the same world.

**Proof.** If $\Diamond p$ holds at $w\in W$, choose a designated successor
$y$ satisfying $p$. For any other designated successor $z$, Euclideanity gives
$R(z,y)$, so $\Diamond p$ holds at $z$. Thus $\Box\Diamond p$ holds at $w$.
Conversely, suppose $w,y,z\in W$ with $R(w,y)$ and $R(w,z)$. Make $a$ true
only at $y$. The edge to $y$ gives $\Diamond a$ at $w$. Validity of 5 then
gives $\Diamond a$ at $z$, whose sole possible witness is $y$. Therefore
$R(z,y)$, in exactly the orientation of Section 2. $\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `MODAL_EUCL`.

## 5. Löb's axiom and converse well-foundedness

### 5.1 Correspondence theorem

**Statement.** Assume edge closure (C). Then

$$
\operatorname{Transitive}(W,R)\ \land\ \operatorname{WF}(R^{-1})
\quad\Longleftrightarrow\quad
\forall p,\ F\models\Box(\Box p\to p)\to\Box p.
$$

**Comment.** The well-foundedness condition is on the full converse relation
on $D$. Under (C), all endpoints of its edges lie in $W$. It rules out
self-loops as well as infinite forward accessibility chains: in particular,
a self-loop would leave its singleton with no $R^{-1}$-minimal member.
Transitivity and irreflexivity alone are not the displayed condition on an
infinite frame.

**Proof, relational conditions imply validity.** Fix a valuation and formula
$p$. Suppose $\Box(\Box p\to p)$ holds at $w\in W$. We must prove $p$ at
each designated successor of $w$.

Use well-founded induction along $R^{-1}$ on $y$, with the induction
assertion

$$
y\in W\land R(w,y)\Longrightarrow F,V,y\models p.
$$

Take such a $y$. To prove $p$ there, the boxed assumption at $w$ supplies
$\Box p\to p$ at $y$. For every designated successor $z$ of $y$,
transitivity gives $R(w,z)$. The induction hypothesis at $z$ therefore gives
$p$ at $z$. This establishes $\Box p$ at $y$, and hence $p$ there. The
induction proves $\Box p$ at $w$.

**Proof, validity implies transitivity.** Assume all Löb instances are valid.
Fix $w,y,z\in W$ with $R(w,y)$ and $R(y,z)$. Interpret an atom $a$ by

$$
U(u)\iff u\in W\land R(w,u)\land
\forall v\in W,\ R(u,v)\Longrightarrow R(w,v).
$$

At each designated successor $u$ of $w$, suppose $\Box a$ holds. Every
designated successor $v$ of $u$ then satisfies $U(v)$, which in particular
gives $R(w,v)$. Together with $u\in W$ and $R(w,u)$, this proves $U(u)$.
Thus $\Box(\Box a\to a)$ holds at $w$. Löb validity gives $\Box a$ at
$w$, so $U(y)$. Its last conjunct applied to $z$ gives $R(w,z)$.

**Proof, validity implies converse well-foundedness.** If $R^{-1}$ were
not well founded, classical dependent choice would give a sequence
$x_0Rx_1Rx_2R\cdots$. Condition (C) puts each $x_n$ in $W$. Make an atom
$a$ true exactly outside the range of this sequence.

At any designated successor $u$ of $x_0$, the implication $\Box a\to a$
holds. If $u$ is outside the range, its consequent is true. If $u=x_n$,
its successor $x_{n+1}$ is in the range and falsifies $a$, so $\Box a$
is false. Consequently $\Box(\Box a\to a)$ holds at $x_0$. But
$\Box a$ fails there because $x_1$ is an accessible designated world where
$a$ is false. This contradicts validity of Löb's axiom. The sequence need
not be injective for this argument. $\square$

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `MODAL_TRANSNT`.
The statement, including (C), agrees in the two files. The chain argument
for the last direction follows Lean; HOL Light establishes well-foundedness
through its induction characterization.

## 6. Grzegorczyk's axiom and weak converse well-foundedness

### 6.1 Correspondence theorem

**Statement.** Assume edge closure (C). Then

$$
\operatorname{Reflexive}(W,R)\ \land\
\operatorname{Transitive}(W,R)\ \land\ \operatorname{WWF}(R^{-1})
\quad\Longleftrightarrow\quad
\forall p,\ F\models\Box(\Box(p\to\Box p)\to p)\to p.
$$

**Comment.** Unlike Löb's condition, weak converse well-foundedness permits
self-loops. It prevents endless progress through distinct successors.
The converse proof first extracts reflexivity, transitivity, and
antisymmetry, then uses an alternating valuation on a hypothetical infinite
chain. These intermediate properties are essential to make that valuation
well defined.

**Formalization references.** [HOL Light](../ad_hoc_correspondence.ml) and
[Lean](../lean/HOLMS/AdHocCorrespondence.lean): `MODAL_RTWN`.
Sections 6.2–6.5 are parts of its proof, not separately named declarations.

### 6.2 The relational conditions imply validity

Fix a formula $p$ and a valuation. For brevity put

$$
A=\Box(\Box(p\to\Box p)\to p).
$$

Transitivity gives a persistence fact: if $A$ holds at $w\in W$ and
$R(w,u)$ with $u\in W$, then $A$ holds at $u$. Indeed every designated
successor of $u$ is a successor of $w$, where the content of the outer box
holds.

Define two sets of designated worlds:

$$
X_0=\{w\in W:F,V,w\models A\ \land\ F,V,w\not\models p\},
$$

$$
X_1=\{w\in W:F,V,w\models A\ \land\ F,V,w\models p
                         \ \land\ F,V,w\not\models\Box p\}.
$$

They are disjoint because $p$ is false in $X_0$ and true in $X_1$.
Every member of either set has a successor in the other:

- If $w\in X_0$, reflexivity and $A$ give $\Box(p\to\Box p)\to p$
  at $w$. Since $p$ is false there, $\Box(p\to\Box p)$ is false. Choose
  a designated successor $u$ where $p$ is true and $\Box p$ is false.
  Persistence of $A$ gives $u\in X_1$.
- If $w\in X_1$, failure of $\Box p$ gives a designated successor $u$
  where $p$ is false. Persistence again gives $A$ at $u$, so $u\in X_0$.

Let $X=X_0\cup X_1$. Reflexivity ensures $W\subseteq\operatorname{fld}(R^{-1})$,
so $X$ lies in that field. If $X$ were nonempty, weak converse
well-foundedness would give a member with no distinct $R$-successor in $X$.
The preceding two constructions always supply such a successor, and it is
distinct because it lies in the opposite, disjoint set. This is a
contradiction. Hence $X_0$ is empty: wherever $A$ holds at a designated
world, $p$ holds too. This proves Grzegorczyk validity.

This proof follows HOL Light's two-set argument. Lean instead uses
well-founded induction on the relation $u\ne w\land R(w,u)$, justified
by the bridge in Section 3.2.

### 6.3 Validity forces reflexivity and transitivity

Assume all Grzegorczyk instances are valid.

**Reflexivity.** Fix $w\in W$ and interpret an atom $a$ by
$U(u)\iff R(w,u)$. Every designated successor of $w$ satisfies $a$, and
therefore satisfies $\Box(a\to\Box a)\to a$. Thus
$\Box(\Box(a\to\Box a)\to a)$ holds at $w$. Grzegorczyk validity gives
$a$ at $w$, meaning $R(w,w)$.

**Transitivity.** Suppose $x,y,z\in W$ satisfy $R(x,y)$ and $R(y,z)$ but
not $R(x,z)$. Make $a$ true exactly when

$$
U(u)\iff u\ne x\land R(x,u).
$$

It is false at $x$ and $z$, but true at $y$: equality $y=x$ would turn
$R(y,z)$ into the excluded edge $R(x,z)$. We show that the Grzegorczyk
antecedent holds at $x$. For any designated successor $u\ne x$, $a$ is
true, so $\Box(a\to\Box a)\to a$ holds. If $u=x$, the successor $y$
satisfies $a$ but not $\Box a$, because it sees $z$. Consequently
$\Box(a\to\Box a)$ is false at $x$, making the same implication true
there as well. The outer box therefore holds at $x$, while $a$ is false
there, contradicting validity. Hence transitivity holds.

### 6.4 Validity forces antisymmetry

Suppose $x,y\in W$ are distinct and $R(x,y),R(y,x)$. Make $a$ true at all
points except $x$. At each designated successor $u\ne x$ of $x$, the
implication $\Box(a\to\Box a)\to a$ holds because its consequent is true.
At $x$, it also holds: its antecedent is false, since $y$ is a successor
satisfying $a$ but not $\Box a$ (it sees $x$). Thus the outer Grzegorczyk
antecedent holds at $x$, but $a$ is false there. This contradicts validity.
Therefore

$$
\forall x,y\in W,\quad R(x,y)\land R(y,x)\Longrightarrow x=y.
$$

This intermediate consequence will prevent repetitions on a chain of
successive distinct worlds. It is proved locally within `MODAL_RTWN` in
both sources.

### 6.5 Validity forces weak converse well-foundedness

Suppose, for a contradiction, that $\operatorname{WWF}(R^{-1})$ fails.
By Section 3.2, the relation

$$
Q(y,x)\iff y\ne x\land R(x,y)
$$

is not well founded. Classical dependent choice gives a sequence $(x_n)$
with $R(x_n,x_{n+1})$ and $x_{n+1}\ne x_n$ for every $n$. By (C), all
these points lie in $W$.

Reflexivity and transitivity imply $R(x_i,x_j)$ whenever $i\le j$:
induct on $j-i$, starting with reflexivity and appending one chain edge.
The sequence is injective. Indeed, if $i<j$ and $x_i=x_j$, reachability
from $x_{i+1}$ to $x_j$ gives $R(x_{i+1},x_i)$. Together with
$R(x_i,x_{i+1})$, antisymmetry forces $x_i=x_{i+1}$, contradicting the
choice of the chain. The case $j<i$ is symmetric.

Interpret an atom $a$ by

$$
U(u)\iff u\notin\{x_{2n}:n\in\mathbb N\}.
$$

Thus $a$ is false at the even-indexed chain points and true at every
odd-indexed point, as injectivity ensures. It is also true away from the
even-indexed points.

We show that $\Box(\Box(a\to\Box a)\to a)$ holds at $x_0$. Take any
designated successor $u$ of $x_0$. If $a$ holds at $u$, the inner
implication is immediate. Otherwise $u=x_{2n}$ for some $n$. Its successor
$x_{2n+1}$ satisfies $a$, but not $\Box a$, since it sees $x_{2n+2}$,
where $a$ is false. Hence $\Box(a\to\Box a)$ is false at $u$, and again
$\Box(a\to\Box a)\to a$ is true there. This proves the outer box at
$x_0$, whereas $a$ is false at $x_0$. Grzegorczyk validity is contradicted.
Consequently $\operatorname{WWF}(R^{-1})$ holds, completing the converse
and the correspondence proof. $\square$

The injective-chain presentation follows Lean. HOL Light uses dependent
choice and tracks first occurrences along the chain to construct its
alternating valuation; the semantic contradiction has the same form.

## 7. Overview and use in frame classes

The correspondences can be collected as follows. Each row means validity of
all instances of the indicated schema, not merely one formula under a fixed
valuation.

| Schema | Equivalent relational condition | Additional hypothesis |
|---|---|---|
| D | Seriality on $W$ | None |
| T | Reflexivity on $W$ | None |
| 4 | Transitivity on $W$ | None |
| B | Symmetry on $W$ | None |
| 5 | Euclideanity on $W$ | None |
| Löb | Transitivity on $W$ and $\operatorname{WF}(R^{-1})$ | Edge closure (C) |
| Grzegorczyk | Reflexivity and transitivity on $W$, and $\operatorname{WWF}(R^{-1})$ | Edge closure (C) |

These results identify the semantic conditions imposed by individual axiom
schemata. Combined with the characteristic-frame definitions and generic
soundness of [ParametricCorrespondence](ParametricCorrespondence.md), they
provide the relational descriptions used in subsequent system-specific
results. They do not themselves prove completeness or the finite-model
property of any modal system.
