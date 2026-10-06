# Parametric correspondence and soundness in HOLMS

This chapter connects an arbitrary set of modal axioms with the classes of
Kripke frames that validate it. It establishes soundness of the calculus on
those classes and identifies the finite frames that validate all theorems.
Definitions, mathematical statements, and informal proofs are presented
together; no knowledge of a proof assistant is assumed.

The prerequisites are [modal syntax and semantics](Modal.md) and the
[axiomatic calculus](Calculus.md). See the
[mathematical documentation index](README.md) for the other chapters.
The formal developments are
[HOL Light's `parametric_correspondence.ml`](../parametric_correspondence.ml)
and [Lean's `HOLMS/ParametricCorrespondence.lean`](../lean/HOLMS/ParametricCorrespondence.lean).
Names in each **Formalization references** paragraph occur in both files
unless stated otherwise; Lean names are relative to namespace `HOLMS`.
Representation and proof-engineering choices are described in the
[ParametricCorrespondence translation notes](../lean/translation/ParametricCorrespondence.md).

## 1. Notation and scope

Fix an ambient domain $D$. A frame is a pair $F=(W,R)$ with $W\subseteq D$
and $R\subseteq D\times D$. The designated worlds are the members of $W$;
they need not exhaust $D$. A valuation $V$ interprets atoms on $D$, and
$F,V,w\models p$ denotes satisfaction. In particular,

$$
F,V,w\models\Box p
\iff
\forall v\in W,\ R(w,v)\Longrightarrow F,V,v\models p.
$$

Frame validity and class validity mean

$$
F\models p\iff\forall V\,\forall w\in W,\ F,V,w\models p,
\qquad
\mathcal X\models p\iff\forall F\in\mathcal X,\ F\models p.
$$

All frame classes below are over the same fixed $D$; their definitions and
results are parametric in that domain. Let $\mathcal F$ denote the set of
modal formulas and $S,H\subseteq\mathcal F$. As in the calculus chapter,
$S;H\vdash p$ means derivability with additional global axioms $S$ and local
hypotheses $H$. The necessitation rule has the form

$$
\frac{S;\varnothing\vdash p}{S;H\vdash\Box p}.
$$

Write $\mathsf{Ax}_K$ for the set of instances of the eleven primitive
axiom schemata listed in [Calculus](Calculus.md).

Here *parametric correspondence* associates $S$ with a class of frames by
validity. It does not yet identify particular modal axioms with relational
conditions such as reflexivity or transitivity. Nor does it assert that every
formula valid in a characteristic class is derivable: that converse would be
a completeness theorem.

## 2. Well-formed and finite frames

### 2.1 Well-formedness

Define the class of **well-formed frames** over $D$ by

$$
\mathsf{Fr}_D=
\{(W,R):W\ne\varnothing\ \text{and}\ R\subseteq W\times W\}.
$$

**Statement.** For every frame $F=(W,R)$,

$$
F\in\mathsf{Fr}_D
\iff
W\ne\varnothing\ \land\
\forall x,y\in D,\ R(x,y)\Longrightarrow(x\in W\ \land\ y\in W).
$$

**Comment.** The bare frames of the syntax-and-semantics chapter may have
empty world sets or accessibility edges outside them. Membership in
$\mathsf{Fr}_D$ adds nonemptiness and requires both endpoints of every edge
to be designated worlds. It does not require every pair of worlds to be
related.

**Proof.** Unfold the definition of $\mathsf{Fr}_D$. The inclusion
$R\subseteq W\times W$ says precisely that each related pair has both
coordinates in $W$. $\square$

**Formalization references.**
[HOL Light](../parametric_correspondence.ml): `FRAME_DEF` defines `FRAME`;
[Lean](../lean/HOLMS/ParametricCorrespondence.lean): `FRAME`.
The membership theorem is `IN_FRAME` in both files. HOL Light writes
$W\ne\varnothing$; Lean uses nonemptiness of the designated set.

### 2.2 Finite well-formed frames

Define

$$
\mathsf{FinFr}_D=
\{F=(W,R):F\in\mathsf{Fr}_D\ \text{and}\ |W|<\infty\}.
$$

**Statements.** For every frame $F=(W,R)$,

$$
F\in\mathsf{FinFr}_D
\iff
W\ne\varnothing\ \land\
\bigl(\forall x,y\in D,\ R(x,y)\Longrightarrow(x\in W\land y\in W)\bigr)
\ \land\ |W|<\infty,
$$

and, equivalently,

$$
F\in\mathsf{FinFr}_D\iff(F\in\mathsf{Fr}_D\ \land\ |W|<\infty).
$$

**Comment.** Only the designated world set must be finite. The ambient domain
$D$ may be infinite, allowing a finite frame to be represented inside a larger
domain.

**Proof.** The second equivalence is the definition. Substitute the
well-formedness characterization of Section 2.1 into it and regroup the
conjunctions to obtain the first. $\square$

**Formalization references.**
[HOL Light](../parametric_correspondence.ml): `FINITE_FRAME_DEF` defines
`FINITE_FRAME`; [Lean](../lean/HOLMS/ParametricCorrespondence.lean):
`FINITE_FRAME`. Both files provide `IN_FINITE_FRAME` for the expanded
characterization and `IN_FINITE_FRAME_INTER` for the second equivalence.

### 2.3 Inclusion of finite frames

**Statement.**

$$
\mathsf{FinFr}_D\subseteq\mathsf{Fr}_D.
$$

**Proof.** If $F\in\mathsf{FinFr}_D$, Section 2.2 supplies both
$F\in\mathsf{Fr}_D$ and finiteness of its designated worlds. Keep the first
conjunct. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean):
`FINITE_FRAME_SUBSET_FRAME`.

## 3. Frames characteristic for an axiom set

For any set $S$ of formulas, define its **characteristic class** by

$$
\mathsf{Char}_D(S)=
\{F\in\mathsf{Fr}_D:\forall p\in S,\ F\models p\}.
$$

Thus every selected axiom must hold under every valuation at every designated
world of each characteristic frame. No closure of $S$ under substitution is
assumed in this chapter.

### 3.1 Membership in the characteristic class

**Statement.** For every $S$ and frame $F$,

$$
F\in\mathsf{Char}_D(S)
\iff
F\in\mathsf{Fr}_D\ \land\ \forall p\in S,\ F\models p.
$$

**Proof.** This is the defining membership condition for
$\mathsf{Char}_D(S)$. $\square$

**Formalization references.**
[HOL Light](../parametric_correspondence.ml): `CHAR_DEF` defines `CHAR`;
[Lean](../lean/HOLMS/ParametricCorrespondence.lean): `CHAR`.
Both provide the membership theorem `IN_CHAR`.

## 4. Validity of the axioms

### 4.1 Primitive K axioms are valid on every frame

**Statement.** For every frame $F$ and formula $p$,

$$
p\in\mathsf{Ax}_K\Longrightarrow F\models p.
$$

**Comment.** No well-formedness or finiteness assumption on $F$ is needed.
This stronger framewise fact is the base case for generic soundness.

**Proof.** Fix a valuation $V$ and a designated world $w$. Inspect the axiom
schema that produces $p$.

For the ten propositional schemata, evaluate their component formulas at
$w$ and use the classical clauses of satisfaction:

- Antecedent introduction $a\to(b\to a)$ preserves the truth of $a$.
  For implication distribution, if $a\to(b\to c)$, $a\to b$, and $a$
  hold, first obtain $b\to c$ and $b$, then $c$.
- Classical double-negation elimination $((a\to\bot)\to\bot)\to a$
  holds because if $a$ were false, $a\to\bot$ would be true, contradicting
  the antecedent.
- The two biconditional projections extract one of its implications.
  Conversely, the two implications ensure that the component formulas have
  the same truth value, proving biconditional introduction.
- The truth axiom equates two true formulas, $\top$ and $\bot\to\bot$.
  The negation axiom says that $a$ is false exactly when $a\to\bot$ is true.
- For conjunction, $a\to(b\to\bot)$ is false exactly when both $a$ and
  $b$ are true. Its implication to $\bot$ is therefore true exactly when
  $a\land b$ is true. For disjunction, $a\lor b$ is true exactly when it
  is not the case that both $a$ and $b$ are false, giving
  $(a\lor b)\leftrightarrow\neg(\neg a\land\neg b)$.

For the modal schema, assume $F,V,w\models\Box(a\to b)$ and
$F,V,w\models\Box a$. Take any $v\in W$ with $R(w,v)$. The first boxed
assumption gives $a\to b$ at $v$, and the second gives $a$ there; hence
$b$ holds at $v$. Since $v$ was arbitrary, $\Box b$ holds at $w$.
This proves $\Box(a\to b)\to(\Box a\to\Box b)$.

The valuation and designated world were arbitrary, so every axiom instance
is valid in $F$. $\square$

**Formalization references.**
[Lean](../lean/HOLMS/ParametricCorrespondence.lean): `KAXIOM_HOLDS_IN`.
There is no separately named counterpart in
[HOL Light](../parametric_correspondence.ml); the same semantic argument
is used inside `GEN_KAXIOM_CHAR_VALID` and `GEN_KAXIOM_SUBS_CHAR_VALID`.

### 4.2 Primitive axioms on characteristic classes and subclasses

**Statements.** For every $S,p$,

$$
p\in\mathsf{Ax}_K\Longrightarrow\mathsf{Char}_D(S)\models p.
$$

For every class $\mathcal X$,

$$
\mathcal X\subseteq\mathsf{Char}_D(S),\quad p\in\mathsf{Ax}_K
\quad\Longrightarrow\quad\mathcal X\models p.
$$

**Proof.** Choose any frame in the indicated class and apply Section 4.1.
The result holds for every frame of that class, which is precisely class
validity. $\square$

**Comment.** The subclass condition in the second formal statement is
unnecessary for primitive axioms: Section 4.1 works for any frame class.
It is retained in that interface to match the additional-axiom and soundness
results below. Here and below, `SUBS` in theorem names refers to subclasses,
not to uniform substitution.

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean):
`GEN_KAXIOM_CHAR_VALID`, `GEN_KAXIOM_SUBS_CHAR_VALID`, respectively.

### 4.3 Additional axioms on characteristic classes and subclasses

**Statements.**

$$
p\in S\Longrightarrow\mathsf{Char}_D(S)\models p,
$$

$$
\mathcal X\subseteq\mathsf{Char}_D(S),\quad p\in S
\quad\Longrightarrow\quad\mathcal X\models p.
$$

**Proof.** A frame in $\mathsf{Char}_D(S)$ validates every member of $S$
by Section 3.1, and therefore validates $p$. For the second statement,
a frame in $\mathcal X$ belongs to $\mathsf{Char}_D(S)$ by inclusion, so
the same argument applies. Quantify over the selected class. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean):
`GEN_AX_CHAR_VALID`, `GEN_AX_SUBS_CHAR_VALID`.

## 5. Generic soundness

### 5.1 Soundness on a subclass of characteristic frames

**Statement.** Let $\mathcal X\subseteq\mathsf{Char}_D(S)$. For every local
context $H$ and formula $p$,

$$
S;H\vdash p,\quad\forall q\in H,\ \mathcal X\models q
\quad\Longrightarrow\quad\mathcal X\models p.
$$

**Comment.** Here the local hypotheses are assumed **valid on the entire
class**: each holds at every designated world under every valuation of every
frame in $\mathcal X$. This is the statement proved by these declarations;
it is not phrased merely as preservation of truth from hypotheses at a
single chosen world. With $H=\varnothing$, the hypothesis-validity condition
is vacuous, giving soundness for theorems.

**Proof.** Fix $S$ and $\mathcal X\subseteq\mathsf{Char}_D(S)$. Induct on
the derivation of $S;H\vdash p$, keeping the assertion conditional on the
validity of every member of the derivation's local context. That context may
change in a necessitation premise.

- **Primitive axiom.** Section 4.2 gives validity on $\mathcal X$.
- **Additional axiom.** If $p\in S$, Section 4.3 gives validity on
  $\mathcal X$.
- **Local hypothesis.** If $p\in H$, use the assumed validity of members
  of $H$.
- **Modus ponens.** Suppose the last step derives $b$ from $a\to b$ and
  $a$ in the same context. The two induction hypotheses give
  $\mathcal X\models a\to b$ and $\mathcal X\models a$. At any frame
  $F\in\mathcal X$, valuation $V$, and designated world $w$, both hold;
  the implication clause of satisfaction gives $F,V,w\models b$.
  Quantifying over $F,V,w$ yields $\mathcal X\models b$.
- **Necessitation.** Suppose the last step derives $\Box a$ from
  $S;\varnothing\vdash a$. Apply the induction hypothesis to this premise:
  there are no local hypotheses whose validity must be supplied, so it gives
  $\mathcal X\models a$. Fix $F=(W,R)\in\mathcal X$, a valuation $V$,
  and $w\in W$. For every $v\in W$ with $R(w,v)$, class validity gives
  $F,V,v\models a$. Thus $F,V,w\models\Box a$. Quantifying over $F,V,w$
  gives validity of the conclusion.

All derivation rules preserve the required property. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean):
`GEN_SUBS_CHAR_VALID`.

### 5.2 Soundness on the characteristic class

**Statement.**

$$
S;H\vdash p,\quad\forall q\in H,\ \mathsf{Char}_D(S)\models q
\quad\Longrightarrow\quad\mathsf{Char}_D(S)\models p.
$$

In particular,

$$
S;\varnothing\vdash p\Longrightarrow\mathsf{Char}_D(S)\models p.
$$

**Proof.** Apply Section 5.1 with
$\mathcal X=\mathsf{Char}_D(S)$, using reflexivity of inclusion. For the
empty-context consequence, the requirement on members of $H$ has no
instances. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean): `GEN_CHAR_VALID`.
The empty-context statement is its specialization, not a separate named
theorem in these files. HOL Light proves the general statement directly by
derivation induction; Lean obtains it from the subclass theorem.

## 6. Characteristic frames and validity of all theorems

### 6.1 Characterization by all derivable theorems

**Statement.** For every $S$ and frame $F$,

$$
\bigl(F\in\mathsf{Fr}_D\ \land\
\forall p\in\mathcal F,\ S;\varnothing\vdash p\Longrightarrow F\models p\bigr)
\quad\Longleftrightarrow\quad F\in\mathsf{Char}_D(S).
$$

**Comment.** Among well-formed frames, validating the chosen axioms is
equivalent to validating all their derivable theorems. A characteristic
frame can validate additional formulas; the statement does not identify
its entire set of valid formulas with the set of derivable formulas.
This characterization is the link needed to compare the two frame classes
in Section 7.

**Proof.** Suppose first that $F$ is well formed and validates every theorem
of $S$. If $p\in S$, additional-axiom introduction gives
$S;\varnothing\vdash p$, so $F\models p$. Hence $F$ validates every member
of $S$ and belongs to $\mathsf{Char}_D(S)$ by Section 3.1.

Conversely, let $F\in\mathsf{Char}_D(S)$. It is well formed by definition.
If $S;\varnothing\vdash p$, empty-context soundness (Section 5.2) gives
$\mathsf{Char}_D(S)\models p$. Apply this class-validity statement to $F$
to obtain $F\models p$. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean): `CHAR_CAR`.

## 7. Finite frames appropriate for an axiom set

Define the class of **appropriate frames** for $S$ by

$$
\mathsf{Appr}_D(S)=
\{F\in\mathsf{FinFr}_D:
\forall p\in\mathcal F,\ S;\varnothing\vdash p\Longrightarrow F\models p\}.
$$

Thus appropriateness initially asks for validity of every theorem, rather
than just each selected axiom, and includes finiteness and well-formedness.

### 7.1 Membership in the appropriate class

**Statement.**

$$
F\in\mathsf{Appr}_D(S)
\iff F\in\mathsf{FinFr}_D\ \land\
\forall p\in\mathcal F,\ S;\varnothing\vdash p\Longrightarrow F\models p.
$$

**Proof.** Unfold the definition of $\mathsf{Appr}_D(S)$. $\square$

**Formalization references.**
[HOL Light](../parametric_correspondence.ml): `APPR_DEF` defines `APPR`;
[Lean](../lean/HOLMS/ParametricCorrespondence.lean): `APPR`.
Both provide the membership theorem `IN_APPR`.

### 7.2 Appropriate frames are exactly finite characteristic frames

**Statement.** For every $S$ and $F=(W,R)$,

$$
F\in\mathsf{Appr}_D(S)
\iff F\in\mathsf{Char}_D(S)\ \land\ |W|<\infty.
$$

**Comment.** Soundness reduces the apparent requirement to validate all
theorems to the requirement to validate the axioms. Only the separate
finiteness condition remains.

**Proof.** If $F$ is appropriate, it is a finite well-formed frame and
validates every theorem. By Section 6.1, the latter two properties make it
characteristic; its world set is already finite.
Conversely, suppose $F$ is characteristic and $W$ is finite. Characteristic
membership gives well-formedness and, by Section 6.1, validity of every
theorem. Well-formedness together with finiteness gives
$F\in\mathsf{FinFr}_D$, so Section 7.1 yields appropriateness. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean): `APPR_CAR`.

### 7.3 Appropriate frames as an intersection

**Statement.** For every $S$,

$$
\mathsf{Appr}_D(S)=\mathsf{Char}_D(S)\cap\mathsf{FinFr}_D.
$$

**Proof.** Compare membership of an arbitrary frame $F=(W,R)$ in the two
sides. Section 7.2 identifies the left side with characteristic membership
and finiteness of $W$. Characteristic membership already includes
well-formedness, so adjoining finiteness is equivalent to requiring
$F\in\mathsf{FinFr}_D$. This is exactly membership in the right-hand
intersection. Extensionality gives equality of the classes. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean):
`APPR_EQ_CHAR_FINITE`.

### 7.4 Inclusion in the characteristic class

**Statement.**

$$
\mathsf{Appr}_D(S)\subseteq\mathsf{Char}_D(S).
$$

**Proof.** By Section 7.2, appropriate membership includes characteristic
membership. Equivalently, project the first component of the intersection
in Section 7.3. $\square$

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean): `APPR_SUBSET_CHAR`.

### 7.5 Soundness on appropriate frames

**Statement.**

$$
S;\varnothing\vdash p\Longrightarrow\mathsf{Appr}_D(S)\models p.
$$

**Proof.** Fix an appropriate frame $F$. Its defining property says that it
validates every empty-context theorem of $S$, so it validates the given $p$.
Since $F$ was arbitrary, $p$ is valid on the class. Alternatively, apply
empty-context soundness on characteristic frames and restrict along the
inclusion of Section 7.4. $\square$

**Comment.** This is soundness on a finite-frame class, not finite-frame
completeness. Neither the converse implication nor the existence of an
appropriate frame for an arbitrary $S$ is asserted. If the class is empty,
its validity statements hold vacuously.

**Formalization references.** [HOL Light](../parametric_correspondence.ml)
and [Lean](../lean/HOLMS/ParametricCorrespondence.lean): `GEN_APPR_VALID`.

## 8. Role in the wider development

The characteristic class ties an arbitrary axiom set to its semantic models.
Generic soundness propagates axiom validity through derivations, and
`CHAR_CAR` makes validation of axioms interchangeable with validation of all
theorems on well-formed frames. The appropriate class adds finiteness to this
same condition. These facts let later developments prove relational
correspondences and completeness for particular systems while reusing the
parametric soundness argument.
