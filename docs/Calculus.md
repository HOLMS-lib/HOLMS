# The modal axiomatic calculus of HOLMS

This chapter presents the Hilbert calculus and its derived rules in ordinary
mathematical language. Statements and informal proofs are kept together; no
knowledge of a proof assistant is assumed.

See the [mathematical documentation index](README.md) and the companion
chapter on [syntax and semantics](Modal.md). The formal developments are
[HOL Light's `calculus.ml`](../calculus.ml) and
[Lean's `HOLMS/Calculus.lean`](../lean/HOLMS/Calculus.lean).
Each **Formalization references** paragraph below gives names in both files
unless it explicitly distinguishes them. Lean names are relative to namespace
`HOLMS`. Historical spellings are retained so that declarations can be found
exactly. Implementation details belong in the
[Calculus translation notes](../lean/translation/Calculus.md).
The [obsolete Italian version](Calculus.it.obsolete.md) is retained for
historical reference and is no longer maintained.

## 1. Language, judgments, and proof conventions

The formulas are those of the modal language described in [Modal](Modal.md):
$\bot,\top$, atoms, $\neg,\land,\lor,\to,\leftrightarrow$, and $\Box$.
Possibility abbreviates $\Diamond p=\neg\Box\neg p$.
All propositional connectives are primitive syntax; the axioms below govern
their deductive behaviour.

The judgment

$$
S;H\vdash p
$$

means that $p$ is derivable from a set $S$ of additional **global axioms**
and a set $H$ of **local hypotheses**. The base calculus is classical normal
modal logic K. Choosing appropriate additional axiom sets gives other modal
systems; for example, the instances of Löb's axiom give GL. Despite the
historical GL heading in the HOL Light source, Löb's axiom is not one of the
primitive axioms listed here. For arbitrary $S$, substitution closure is a
separate condition, made explicit in Section 11.

Unless a context is displayed, $\vdash p$ abbreviates $S;H\vdash p$ for
fixed but arbitrary $S,H$. All formula variables in a statement are universally
quantified. Implication associates to the right. A fraction is a rule between
derivability judgments, not an additional primitive inference rule. In
particular,

$$
\vdash p\leftrightarrow q
\qquad\text{and}\qquad
(\vdash p)\Longleftrightarrow(\vdash q)
$$

are different statements: the former derives a formula, while the latter
compares two derivability claims. We use $\Longrightarrow,\Longleftrightarrow$
between claims and $\to,\leftrightarrow$ inside formulas.

**MP** denotes modus ponens. After Section 4, **DT** denotes the deduction
theorem: a proof under an extra local assumption can be discharged into an
implication. Such informal proofs use weakening to retain previously derived
formulas in enlarged contexts. These are syntactic arguments within the
calculus, not appeals to semantic completeness.

## 2. Primitive axioms and inference rules

### 2.1 The eleven axiom schemata

Let $\mathsf{Ax}_K$ be the set of all instances of the following schemata.
The last column names the theorem asserting derivability of that instance.

| Meaning | Axiom formula | Name in both formalizations |
|---|---|---|
| Add an antecedent | $p\to(q\to p)$ | `MLK_axiom_addimp` |
| Distribute implication | $(p\to(q\to r))\to((p\to q)\to(p\to r))$ | `MLK_axiom_distribimp` |
| Classical double-negation elimination | $((p\to\bot)\to\bot)\to p$ | `MLK_axiom_doubleneg` |
| First biconditional projection | $(p\leftrightarrow q)\to(p\to q)$ | `MLK_axiom_iffimp1` |
| Second biconditional projection | $(p\leftrightarrow q)\to(q\to p)$ | `MLK_axiom_iffimp2` |
| Biconditional introduction | $(p\to q)\to((q\to p)\to(p\leftrightarrow q))$ | `MLK_axiom_impiff` |
| Truth | $\top\leftrightarrow(\bot\to\bot)$ | `MLK_axiom_true` |
| Negation | $\neg p\leftrightarrow(p\to\bot)$ | `MLK_axiom_not` |
| Conjunction | $(p\land q)\leftrightarrow((p\to(q\to\bot))\to\bot)$ | `MLK_axiom_and` |
| Disjunction | $(p\lor q)\leftrightarrow\neg(\neg p\land\neg q)$ | `MLK_axiom_or` |
| Modal distribution K | $\Box(p\to q)\to(\Box p\to\Box q)$ | `MLK_axiom_boximp` |

**Statement.** For each formula $a$ in the table, and every $S,H$,
$S;H\vdash a$.

**Proof.** Each formula is an instance in $\mathsf{Ax}_K$; apply primitive
axiom introduction from Section 2.2. $\square$

**Comment.** Double-negation elimination makes the propositional basis
classical. The last schema, together with necessitation, governs normal
modal reasoning.

**Formalization references.** [HOL Light](../calculus.ml): `KAXIOM_RULES`
defines `KAXIOM`; [Lean](../lean/HOLMS/Calculus.lean): `KAxiom`.
The eleven names in the table occur in both files.

### 2.2 Defining rules of derivability

Derivability is the least relation closed under these five rules:

$$
\frac{p\in\mathsf{Ax}_K}{S;H\vdash p},\qquad
\frac{p\in S}{S;H\vdash p},\qquad
\frac{p\in H}{S;H\vdash p},
$$

$$
\frac{S;H\vdash p\to q\qquad S;H\vdash p}{S;H\vdash q},
\qquad
\frac{S;\varnothing\vdash p}{S;H\vdash\Box p}.
$$

**Comment.** Necessitation requires an empty **local** context, while $S$
remains available. It cannot box an arbitrary conclusion depending on $H$.
Its conclusion may nevertheless be used in any local context.

**Proof of the named rules.** Each displayed rule is a defining clause of
derivability, so its named theorem applies that clause directly. $\square$

**Formalization references.** [HOL Light](../calculus.ml): `MODPROVES_RULES`;
[Lean](../lean/HOLMS/Calculus.lean): `ModProves`. Both provide
`MODPROVES_KAXIOM`, `MODPROVES_AX`, `MODPROVES_HP`, `MLK_modusponens`, and
`MLK_necessitation`, in the displayed order.

### 2.3 Weakening in axioms and hypotheses

**Statements.**

$$
\frac{S\subseteq S'\qquad S;H\vdash p}{S';H\vdash p},
\qquad
\frac{H\subseteq H'\qquad S;H\vdash p}{S;H'\vdash p}.
$$

**Comment.** Adding available axioms or hypotheses preserves every existing
proof.

**Proof.** For axiom weakening, induct on the derivation, for all local
contexts. Primitive axioms and hypotheses remain available; an additional
axiom remains available by $S\subseteq S'$. Reapply MP to the two induction
hypotheses. In the necessitation case, the induction hypothesis transports
its empty-context premise to $S'$, and necessitation gives the conclusion.

For hypothesis weakening, induct on the derivation with the target context
arbitrary. The axiom cases are unchanged, and a hypothesis belongs to $H'$
by inclusion. Reapply MP. A necessitation step retains its original
empty-context premise and can already conclude in $H'$. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MODPROVES_MONO1`, `MODPROVES_MONO2`.

## 3. Basic implicational reasoning

These lemmas are established without DT and provide what is needed to prove it.

### 3.1 Extracting and introducing biconditionals

**Statements.**

$$
\frac{\vdash p\leftrightarrow q}{\vdash p\to q},\qquad
\frac{\vdash p\leftrightarrow q}{\vdash q\to p},\qquad
\frac{\vdash p\to q\qquad\vdash q\to p}{\vdash p\leftrightarrow q}.
$$

**Proof.** Apply MP with the two biconditional projection axioms. For the
third rule, apply MP twice to the biconditional introduction axiom.
The name “antisymmetry” for this rule refers to combining the two directions
of implication. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_iff_imp1`, `MLK_iff_imp2`,
`MLK_imp_antisym`.

### 3.2 Antecedent introduction and implication reflexivity

**Statements.**

$$
\frac{\vdash q}{\vdash p\to q},\qquad \vdash p\to p.
$$

**Proof.** For antecedent introduction, apply MP to $q$ and the axiom
$q\to(p\to q)$. For reflexivity, take the two axiom instances
$p\to((p\to p)\to p)$ and $p\to(p\to p)$. The distribution axiom with
middle formula $p\to p$ combines them, by two MP steps, into $p\to p$.
$\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_add_assum`, `MLK_imp_refl_th`.

### 3.3 Implication under a common antecedent

**Statements.**

$$
\frac{\vdash q\to r}{\vdash(p\to q)\to(p\to r)},
\qquad
\frac{\vdash p\to(p\to q)}{\vdash p\to q}.
$$

**Proof.** For the first rule, antecedent introduction gives
$p\to(q\to r)$; MP with the distribution axiom gives the conclusion.
For contraction, that axiom applied to the premise gives
$(p\to p)\to(p\to q)$; MP with reflexivity finishes. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_add_assum`, `MLK_imp_unduplicate`.

### 3.4 Composition and exchange

**Statements.**

$$
\frac{\vdash p\to q\qquad\vdash q\to r}{\vdash p\to r},
\qquad
\frac{\vdash p\to(q\to r)}{\vdash q\to(p\to r)}.
$$

**Proof.** For composition, lift $q\to r$ under antecedent $p$ by Section 3.3
and apply MP to $p\to q$. For exchange, distribution turns the premise into
$(p\to q)\to(p\to r)$. Compose this with the axiom $q\to(p\to q)$.
$\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_trans`, `MLK_imp_swap`.

### 3.5 Combining two consequences of one premise

**Statement.**

$$
\frac{\vdash p\to q_1\qquad\vdash p\to q_2\qquad
\vdash q_1\to(q_2\to r)}{\vdash p\to r}.
$$

**Proof.** Exchange the antecedents in the third premise and compose with
$p\to q_2$ to get $p\to(q_1\to r)$. Exchange once more and compose with
$p\to q_1$ to get $p\to(p\to r)$. Contraction removes the duplicate
antecedent. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_trans_chain_2`.

### 3.6 Internal composition and extension of conclusions

**Statements.**

$$
\vdash(q\to r)\to((p\to q)\to(p\to r)),
$$

$$
\frac{\vdash p\to q}{\vdash(q\to r)\to(p\to r)},
\qquad
\frac{\vdash p\to(q\to r)\qquad\vdash r\to s}
{\vdash p\to(q\to s)}.
$$

**Proof.** Compose $(q\to r)\to(p\to(q\to r))$ with the distribution
axiom to obtain the first statement. Exchange its first two antecedents
and apply MP to $p\to q$ for the second. For the third, lift $r\to s$
under antecedent $q$ and compose with $p\to(q\to r)$. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_trans_th`, `GLimp_add_concl`,
`MLK_imp_trans2`. The historical prefix `GLimp` imposes no GL-specific axiom.

## 4. The deduction theorem

### 4.1 Inserting a local hypothesis

**Statement.**

$$
S;H\vdash p\to q\Longrightarrow S;H\cup\{p\}\vdash q.
$$

**Proof.** Weaken the given derivation to $H\cup\{p\}$. In that context
$p$ is a hypothesis; MP gives $q$. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MODPROVES_DEDUCTION_LEMMA_INSERT`.

### 4.2 Discharging a member of the context

**Statement.**

$$
S;G\vdash q,\quad p\in G
\quad\Longrightarrow\quad S;G\setminus\{p\}\vdash p\to q.
$$

**Comment.** This is the induction lemma underlying the reverse direction of DT.

**Proof.** Fix $S,p$ and induct on the derivation, allowing $G$ to vary.

- A primitive or additional axiom remains derivable in the reduced context;
  antecedent introduction adds $p$.
- If $q$ is a hypothesis and $q=p$, use implication reflexivity. Otherwise
  $q\in G\setminus\{p\}$, so introduce it and add antecedent $p$.
- If MP derives $b$ from $a\to b$ and $a$, the induction hypotheses give
  $p\to(a\to b)$ and $p\to a$ in the reduced context. The distribution
  axiom and two MP steps give $p\to b$.
- If necessitation derives $\Box a$ from $S;\varnothing\vdash a$, retain
  that original empty-context premise. Necessitation gives $\Box a$ in
  $G\setminus\{p\}$, and antecedent introduction gives $p\to\Box a$.
  The hypothesis being discharged was never used in the premise of this step.

These exhaust the derivation rules. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MODPROVES_DEDUCTION_LEMMA_DELETE`.

### 4.3 Deduction theorem

**Statement.** For arbitrary $S,H,p,q$,

$$
S;H\vdash p\to q\quad\Longleftrightarrow\quad
S;H\cup\{p\}\vdash q.
$$

**Comment.** A local hypothesis can be moved into an implication antecedent.
The global axiom set $S$ is unchanged. The restriction on necessitation is
essential to the discharge argument.

**Proof.** Section 4.1 gives the forward direction. For the reverse, if
$p\notin H$, apply Section 4.2 to $H\cup\{p\}$ and use
$(H\cup\{p\})\setminus\{p\}=H$. If $p\in H$, the given derivation already
has context $H$, and antecedent introduction gives $p\to q$. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MODPROVES_DEDUCTION_LEMMA`.

### 4.4 Internal exchange, insertion, and the Frege rule

**Statements.**

$$
\vdash(p\to(q\to r))\to(q\to(p\to r)),
\qquad
\frac{\vdash p\to r}{\vdash p\to(q\to r)},
$$

$$
\frac{\vdash p\to(q\to r)\qquad\vdash p\to q}{\vdash p\to r}.
$$

**Proof.** For internal exchange, assume $p\to(q\to r)$, apply exchange,
and discharge the assumption by DT. For insertion, compose $p\to r$ with
$r\to(q\to r)$. For the Frege rule, apply MP twice to the distribution
axiom with the two premises. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_swap_th`, `MLK_imp_insert`,
`MLK_frege`.

## 5. Falsity, truth, and classical reasoning

### 5.1 Explosion

**Statements.**

$$
\vdash\bot\to p,\qquad
\frac{\vdash\bot}{\vdash p},\qquad
\vdash(p\to\bot)\to(p\to q).
$$

Also, for every $p$,

$$
\bot\in H\Longrightarrow S;H\vdash p.
$$

**Proof.** Compose the antecedent axiom
$\bot\to((p\to\bot)\to\bot)$ with classical double-negation elimination
to obtain $\bot\to p$. MP gives the rule. Lifting $\bot\to q$ under
antecedent $p$ gives the third statement. If $\bot\in H$, hypothesis
introduction supplies $\bot$, and the rule applies. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_ex_falso_th`, `MLK_ex_falso`,
`MLK_imp_contr_th`, `MODPROVES_EX_FALSO`.

### 5.2 Proof by contradiction and Boolean cases

**Statements.**

$$
\frac{\vdash(p\to\bot)\to p}{\vdash p},\qquad
\frac{\vdash p\to q\qquad\vdash(p\to\bot)\to q}{\vdash q}.
$$

**Proof.** For contradiction, assume $p\to\bot$. The premise gives $p$,
then MP gives $\bot$. DT yields $(p\to\bot)\to\bot$; classical
double-negation elimination gives $p$.
For Boolean cases, assume $q\to\bot$. Composing it with $p\to q$ gives
$p\to\bot$, so the second premise gives $q$, a contradiction. Discharge
$q\to\bot$ and apply double-negation elimination. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_contrad`, `MLK_bool_cases`.

### 5.3 Truth and the definition of negation

**Statements.**

$$
\vdash\top,\qquad
(\vdash\neg p)\Longleftrightarrow(\vdash p\to\bot),\qquad
S;\varnothing\vdash\neg\bot.
$$

**Proof.** Extract $(\bot\to\bot)\to\top$ from the truth axiom and apply
MP with reflexivity. The negation equivalence follows by MP in either
direction of its defining axiom. In the empty context, apply that equivalence
to $\bot\to\bot$ to derive $\neg\bot$. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_truth_th`, `MLK_not_def`,
`MLK_not_false`. The last declaration is stated with empty local context;
weakening permits its use in any $H$.

### 5.4 Contraposition

**Statements.**

$$
\frac{\vdash p\to q}{\vdash\neg q\to\neg p},\qquad
\vdash(p\to q)\to(\neg q\to\neg p).
$$

**Proof.** Composition towards $\bot$ transforms $p\to q$ into
$(q\to\bot)\to(p\to\bot)$ (Section 3.6). Use the defining equivalences
for negation to replace the two implications to $\bot$ by negations.
For the internal statement, assume $p\to q$, apply the rule, and use DT.
$\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_contrapos`, `MLK_contrapos_th`.

### 5.5 Double negation

**Statements.**

$$
\vdash((p\to\bot)\to\bot)\leftrightarrow p,\qquad
\vdash\neg\neg p\leftrightarrow p,
$$

$$
\frac{\vdash\neg\neg p}{\vdash p},\qquad
\frac{\vdash p}{\vdash\neg\neg p},\qquad
(\vdash\neg\neg p)\Longleftrightarrow(\vdash p).
$$

**Proof.** One implication of the first statement is the classical axiom.
For the other, assume $p$ and $p\to\bot$; MP gives $\bot$, and DT twice
gives $p\to((p\to\bot)\to\bot)$. Combine the two implications.
For the second statement, the negation axiom converts $\neg\neg p$ to
$(\neg p\to\bot)$. Under this assumption, assuming $p\to\bot$ gives
$\neg p$ and hence $\bot$, so double-negation elimination gives $p$.
Conversely, under $p$, assuming $\neg p$ gives $\bot$, so DT and the
negation axiom give $\neg\neg p$. Combine these directions. The final
rules and equivalence follow by MP with the two implications. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_not_not_false_th`, `MLK_not_not_th`,
`MLK_DOUBLENEG_CL`, `MLK_DOUBLENEG`, `MLK_DOUBLENEG_IFF`, respectively.

## 6. Conjunction, disjunction, and biconditionals

### 6.1 Conjunction introduction and projections

**Statements.**

$$
\vdash(p\land q)\to p,\qquad\vdash(p\land q)\to q,\qquad
\vdash p\to(q\to(p\land q)),
$$

$$
(\vdash p\land q)\Longleftrightarrow
\bigl((\vdash p)\ \text{and}\ (\vdash q)\bigr).
$$

**Comment.** These recover the familiar conjunction rules from its negative
axiomatic characterization.

**Proof.** From $p\land q$ the defining axiom gives
$(p\to(q\to\bot))\to\bot$. To derive $p$, suppose $p\to\bot$.
Under further assumptions $p,q$ we derive $\bot$; discharging $q,p$ gives
$p\to(q\to\bot)$. This contradicts the displayed consequence of the
conjunction. Discharge $p\to\bot$ and eliminate double negation.
To derive $q$, suppose $q\to\bot$ instead and repeat the argument using $q$
to obtain the inner contradiction. DT discharges the conjunction premise
in each projection.

For introduction, assume $p,q$, then $p\to(q\to\bot)$. Two MP steps give
$\bot$. Discharge the last assumption and use the reverse direction of the
conjunction axiom to obtain $p\land q$. Discharge $q,p$ to obtain the
curried formula. MP with this formula gives conjunction from its components;
MP with the projections gives the converse. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_left_th`, `MLK_and_right_th`,
`MLK_and_pair_th`, `MLK_and`.

### 6.2 Conjunction under a common antecedent

**Statements.**

$$
\frac{\vdash r\to p\qquad\vdash r\to q}{\vdash r\to(p\land q)},
\qquad
\frac{\vdash r\to(p\land q)}{\vdash r\to q\quad\text{and}\quad\vdash r\to p}.
$$

**Proof.** Combine the two premises of introduction with
$p\to(q\to(p\land q))$ using the binary composition rule of Section 3.5.
For elimination, compose with each conjunction projection. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_intro` is introduction;
`MLK_and_add` has the same conclusion with its two premises supplied in
reverse order; `MLK_and_elim` gives the two projections in the displayed
order. `MLK_and_imp_th1` is another instance of the introduction rule,
with $r,p,q$ named $p,q,q'$.

### 6.3 Conjoined antecedents and internal modus ponens

**Statements.**

$$
\frac{\vdash(p\land q)\to r}{\vdash p\to(q\to r)},\qquad
\frac{\vdash p\to(q\to r)}{\vdash(p\land q)\to r},\qquad
\frac{\vdash q\to(p\to r)}{\vdash(p\land q)\to r},
$$

$$
(\vdash p\to(q\to r))\Longleftrightarrow(\vdash(p\land q)\to r),
\qquad
\vdash((p\to q)\land p)\to q.
$$

**Proof.** For the first rule, assume $p,q$, form their conjunction, and
apply the given implication; discharge the assumptions. In the reverse
direction, assume $p\land q$, project its components, and apply the curried
implication twice. The third rule uses the components in the opposite order.
The equivalence collects the first two rules. For internal MP, project
$p\to q$ and $p$ from the assumed conjunction, apply MP, and discharge.
$\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_shunt`, `MLK_ante_conj`,
`MLK_ante_conj2`, `MLK_imp_imp`, `MLK_modusponens_th`.

### 6.4 Biconditionals as pairs of implications

**Statements.**

$$
\vdash(p\leftrightarrow q)\leftrightarrow((p\to q)\land(q\to p)),
$$

$$
(\vdash p\leftrightarrow q)\Longleftrightarrow
\bigl((\vdash p\to q)\ \text{and}\ (\vdash q\to p)\bigr).
$$

**Proof.** Under $p\leftrightarrow q$, extract and conjoin its two
implications. Under the conjunction of implications, project both and use
biconditional introduction. Discharge the assumptions and combine the
directions. The external equivalence is also exactly the combination of the
three rules in Section 3.1. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_iff_def_th`, `MLK_iff_def`.

### 6.5 Reflexivity, symmetry, transitivity, and transport

**Statements.**

$$
\vdash p\leftrightarrow p,\qquad
(\vdash p\leftrightarrow q)\Longleftrightarrow(\vdash q\leftrightarrow p),
$$

$$
\frac{\vdash p\leftrightarrow q\qquad\vdash q\leftrightarrow r}
{\vdash p\leftrightarrow r},\qquad
\vdash(p\leftrightarrow q)\to(q\leftrightarrow p),
$$

$$
\frac{\vdash p\leftrightarrow q\qquad\vdash p}{\vdash q},\qquad
\vdash p\leftrightarrow q\Longrightarrow
\bigl((\vdash p)\Longleftrightarrow(\vdash q)\bigr).
$$

**Proof.** Combine two copies of implication reflexivity for the first
statement. For symmetry, extract the implications and reintroduce the
biconditional in the opposite order; applying this twice gives the external
equivalence. For transitivity, compose the forward implications and the
backward implications separately, then combine them. DT internalizes the
symmetry rule. For transport, extract $p\to q$ and apply MP to $p$; use
$q\to p$ for the converse direction of the last claim. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_iff_refl_th`, `MLK_iff_sym`,
`MLK_iff_trans`, `MLK_iff_sym_th`, `MLK_iff_mp`, `MLK_iff`.
HOL Light's `MLK_iff_sym` states the displayed external equivalence; Lean's
same-named theorem states its forward implication, with the reverse obtained
by exchanging $p,q$. HOL Light defines `MLK_iff_sym_th` twice: its final
binding is the implication displayed above, as in Lean; the earlier binding
is the stronger internal biconditional between the two orders.

### 6.6 Disjunction introduction and transport

**Statements.**

$$
\vdash p\to(p\lor q),\qquad\vdash q\to(p\lor q),\qquad
\frac{\vdash p}{\vdash p\lor q},\qquad
\frac{\vdash q}{\vdash p\lor q},
$$

$$
\frac{\vdash p\to q}{\vdash p\to(q\lor r)},\qquad
\frac{\vdash p\to r}{\vdash p\to(q\lor r)}.
$$

**Proof.** Under $p$, an additional assumption $\neg p\land\neg q$ gives
$\neg p$ by projection and hence $\bot$. DT and the negation axiom give
$\neg(\neg p\land\neg q)$; the disjunction axiom gives $p\lor q$.
Discharge $p$. Starting with $q$ uses the other projection. MP gives the
rules from a derived disjunct. Composition with the corresponding
introduction implication gives the last two rules. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_or_right_th` introduces from $p$,
`MLK_or_left_th` from $q$; the direct rules are `MLK_or_introl`,
`MLK_or_intror`. The last two rules are `MLK_or_transl`, `MLK_or_transr`.

### 6.7 Disjunction elimination

**Statements.**

$$
\frac{\vdash p\to r\qquad\vdash q\to r}{\vdash(p\lor q)\to r},
$$

$$
(\vdash(p\lor q)\to r)\Longleftrightarrow
\bigl((\vdash p\to r)\ \text{and}\ (\vdash q\to r)\bigr),
$$

$$
\frac{\vdash p\lor q\qquad\vdash p\to r\qquad\vdash q\to r}{\vdash r}.
$$

**Proof.** Assume $p\lor q$. Use Boolean cases on $p$, then on $q$,
expressing the negative cases by the negation axiom. If either is true, its
given implication yields $r$. If both are false, conjunction introduction
gives $\neg p\land\neg q$, contradicting the disjunction axiom; explosion
yields $r$. Discharge $p\lor q$. Conversely, compose an implication from
the disjunction with each disjunction introduction to obtain the two branch
implications. The last rule applies MP to the first. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_ante_disj`, `MLK_disj_imp`,
`MLK_or_elim`.

### 6.8 Noncontradiction and excluded middle

**Statements.**

$$
(\vdash p\land\neg p)\Longleftrightarrow(\vdash\bot),\qquad
\frac{\vdash p\qquad\vdash\neg p}{\vdash q},\qquad
\vdash(p\land\neg p)\to\bot,
$$

$$
\vdash p\lor\neg p,\qquad
(\vdash p\lor q)\Longleftrightarrow(\vdash\neg(\neg p\land\neg q)).
$$

**Proof.** Project $p,\neg p$ from a contradiction, convert $\neg p$ to
$p\to\bot$, and apply MP. Conversely, explosion derives both conjuncts
from $\bot$. This also proves the rule from separate contradictory premises;
DT gives the internal implication. For excluded middle, use Boolean cases:
from $p$ introduce the left disjunct, and from $p\to\bot$ first derive
$\neg p$ and then introduce the right disjunct. The final equivalence is MP
in both directions of the disjunction axiom. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_NC`, `MLK_NC_ALT`, `MLK_nc_th`,
`MLK_tnd_th`, `MLK_and_eq_or`.

## 7. Algebraic laws and congruence

### 7.1 Commutativity and associativity of conjunction

**Statements.**

$$
\vdash(p\land q)\leftrightarrow(q\land p),\qquad
(\vdash p\land q)\Longleftrightarrow(\vdash q\land p),
$$

$$
\vdash((p\land q)\land r)\leftrightarrow(p\land(q\land r)),
$$

$$
(\vdash(p\land q)\land r)\Longleftrightarrow(\vdash p\land(q\land r)).
$$

**Comment.** The order and bracketing of conjuncts can be changed within the
calculus, and consequently in derivability claims.

**Proof.** The projections $(p\land q)\to q$ and $(p\land q)\to p$
combine by conjunction introduction under a common antecedent into
$(p\land q)\to(q\land p)$. Exchange $p,q$ for the reverse implication
and introduce the biconditional. For associativity, assume either bracketing,
project $p,q,r$, and reintroduce them in the other bracketing. Discharge and
combine the two implications. Transport through these biconditionals gives
the two external equivalences. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_comm_th`, `MLK_and_comm`,
`MLK_and_assoc_th`, `MLK_and_assoc`.

### 7.2 Commutativity and associativity of disjunction

**Statements.**

$$
(\vdash p\lor q)\Longleftrightarrow(\vdash q\lor p),
$$

$$
\vdash(p\lor(q\lor r))\to((p\lor q)\lor r),\qquad
\vdash((p\lor q)\lor r)\to(p\lor(q\lor r)),
$$

$$
\vdash(p\lor(q\lor r))\leftrightarrow((p\lor q)\lor r),
$$

$$
(\vdash(p\lor q)\lor r)\Longleftrightarrow(\vdash p\lor(q\lor r)).
$$

**Proof.** Eliminate $p\lor q$ by cases and introduce each disjunct on the
opposite side. Repeat with $p,q$ exchanged for the converse. For association,
under $p\lor(q\lor r)$, the $p$ case introduces $p\lor q$ and then the
outer disjunction; in the other branch, split $q\lor r$, introducing the
appropriate target disjunct. The reverse implication splits
$(p\lor q)\lor r$ and reinserts each of $p,q,r$ into the target bracketing.
DT gives the displayed implications; biconditional introduction and transport
give the remaining statements. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_or_comm`, `MLK_or_assoc_left_th`,
`MLK_or_assoc_right_th`, `MLK_or_assoc_th`, `MLK_or_assoc`.

### 7.3 Monotonicity of implication and conjunction

**Statements.**

$$
\frac{\vdash p'\to p\qquad\vdash q\to q'}
{\vdash(p\to q)\to(p'\to q')},
$$

$$
\vdash((p'\to p)\land(q\to q'))\to((p\to q)\to(p'\to q')),
$$

$$
\frac{\vdash p\to p'\qquad\vdash q\to q'}
{\vdash(p\land q)\to(p'\land q')}.
$$

**Comment.** Implication reverses the direction in its antecedent and
preserves it in its consequent. Conjunction preserves both directions.

**Proof.** Under additional assumptions $p\to q$ and $p'$, apply
$p'\to p$, $p\to q$, and $q\to q'$ in succession. Discharge the two
assumptions. For the internal version, start by assuming the conjunction of
the two premises and project them, then discharge that conjunction as well.
For conjunction, assume $p\land q$, project, apply the two given
implications, and conjoin the results; DT finishes. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_mono`, `MLK_imp_mono_th`,
`MLK_and_imp`. HOL Light first binds `MLK_imp_mono_th` to the curried
formula $(p'\to p)\to((q\to q')\to((p\to q)\to(p'\to q')))$;
its final binding has the conjoined antecedent displayed here, matching Lean.

### 7.4 Congruence of the binary propositional connectives

**Statement.** For each $\circ\in\{\land,\lor,\to,\leftrightarrow\}$,

$$
\frac{\vdash p\leftrightarrow p'\qquad\vdash q\leftrightarrow q'}
{\vdash(p\circ q)\leftrightarrow(p'\circ q')}.
$$

**Comment.** Provable equivalence permits replacement inside every binary
propositional connective, even when the equivalences depend on local hypotheses.

**Proof.** For conjunction, extract the forward implications, use conjunction
monotonicity, and repeat with the backward implications. For implication,
use $p'\to p$ and $q\to q'$ in one direction, and $p\to p'$ and
$q'\to q$ in the other, applying implication monotonicity. In each case
combine the two implications.

For disjunction, assume $p\lor q$ and eliminate it by cases. In the first
case transport $p$ to $p'$ and introduce the left disjunct; in the second,
transport $q$ to $q'$ and introduce the right disjunct. Reverse the given
equivalences to prove the converse. For biconditionals, use Section 6.4 to
express each as the conjunction of its two implications, apply the already
proved congruences for implication and conjunction, and return to the
biconditional form. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_subst_th`, `MLK_or_subst_th`,
`MLK_imp_subst`, `MLK_iff_subst`, for the four respective connectives.

### 7.5 Transport through congruences and replacement of one conjunct

**Statements.** Under the premises $\vdash p\leftrightarrow p'$ and
$\vdash q\leftrightarrow q'$,

$$
(\vdash p\land q)\Longleftrightarrow(\vdash p'\land q'),
$$

$$
\frac{\vdash p\to q}{\vdash p'\to q'},\qquad
\frac{\vdash p\leftrightarrow q}{\vdash p'\leftrightarrow q'}.
$$

The one-argument versions include

$$
\vdash(q_1\leftrightarrow q_2)\to
((p\land q_1)\leftrightarrow(p\land q_2)),
$$

$$
\vdash(p_1\leftrightarrow p_2)\to
((p_1\land q)\leftrightarrow(p_2\land q)),
$$

$$
\frac{\vdash q_1\leftrightarrow q_2}
{\vdash(p\lor q_1)\leftrightarrow(p\lor q_2)}.
$$

**Proof.** For the first three claims, apply transport (Section 6.5) to the
corresponding congruence in Section 7.4. For one-argument replacement, use
reflexivity for the unchanged argument and the given equivalence for the
other. In the two conjunction statements, assume that equivalence locally
and discharge it with DT. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_subst`, `MLK_imp_mp_subst`,
`MLK_iff_mp_subst`, `MLK_and_subst_right_th`, `MLK_and_subst_left_th`,
`MLK_or_subst_right`, respectively.

### 7.6 Congruence of negation

**Statements.**

$$
\frac{\vdash p\leftrightarrow q}{\vdash\neg p\leftrightarrow\neg q},
\qquad
\frac{\vdash p\leftrightarrow q\qquad\vdash\neg p}{\vdash\neg q},
$$

$$
(\vdash\neg p\leftrightarrow\neg q)\Longleftrightarrow
(\vdash p\leftrightarrow q).
$$

**Proof.** Contrapose the two implications of the given equivalence and
combine them. Transport through the resulting equivalence gives the second
rule. For the converse direction of the final equivalence, apply negation
congruence again to obtain $\neg\neg p\leftrightarrow\neg\neg q$, and
compose with the double-negation equivalences. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_not_subst`, `MLK_not_subst_th`,
`MLK_iff_not`. Despite its suffix, `MLK_not_subst_th` is a transport rule
with two derivability premises.

## 8. Further classical identities

### 8.1 Idempotence and neutral elements

**Statements.**

$$
\vdash p\leftrightarrow(p\land p),\qquad
\vdash(\top\land p)\leftrightarrow p,\qquad
\vdash(p\land\top)\leftrightarrow p,
$$

$$
\vdash(p\lor\bot)\leftrightarrow p,\qquad
\vdash(\bot\lor p)\leftrightarrow p.
$$

**Proof.** For idempotence, conjoin two copies of $p$ in one direction and
project in the other. For conjunction with truth, project $p$ in one
direction; in the other, combine $p$ with the theorem $\top$. For disjunction
with falsity, eliminate by cases: the $p$ branch is immediate and the $\bot$
branch uses explosion. The reverse direction is disjunction introduction.
DT and biconditional introduction finish each internal identity. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_iff_and_refl`,
`MLK_and_left_true_th`, `MLK_and_rigth_true_th`, `MLK_or_rid_th`,
`MLK_or_lid_th`, respectively (including the source spelling `rigth`).

### 8.2 Equivalence with the contrapositive

**Statements.**

$$
\vdash(p\to q)\leftrightarrow(\neg q\to\neg p),\qquad
(\vdash\neg p\to\neg q)\Longleftrightarrow(\vdash q\to p).
$$

**Proof.** The forward implication of the internal equivalence is internal
contraposition. For the reverse, assume $\neg q\to\neg p$ and $p$.
Assuming $\neg q$ produces $\neg p$, contradicting $p$; hence
$\neg\neg q$, and therefore $q$. Discharge the assumptions and combine
the directions. Transport gives the external equivalence with variables
renamed as displayed. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_contrapos_eq_th`, `MLK_contrapos_eq`.

### 8.3 De Morgan's laws

**Statements.**

$$
\vdash\neg(p\land q)\leftrightarrow(\neg p\lor\neg q),\qquad
\vdash\neg(p\lor q)\leftrightarrow(\neg p\land\neg q).
$$

**Proof.** Apply the disjunction axiom to $\neg p,\neg q$ to obtain
$(\neg p\lor\neg q)\leftrightarrow\neg(\neg\neg p\land\neg\neg q)$.
Conjunction and negation congruence, together with double-negation
elimination, turn its right side into $\neg(p\land q)$; symmetry gives
the first statement.

For the second, contrapose each disjunction introduction: from
$\neg(p\lor q)$ obtain $\neg p$ and $\neg q$, and conjoin them. Conversely,
assume their conjunction and then $p\lor q$. Each disjunct contradicts its
corresponding negation, so disjunction elimination yields $\bot$.
Discharge the disjunction to obtain its negation, then discharge the
conjunction and combine directions. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_de_morgan_and_th`,
`MLK_de_morgan_or_th`.

### 8.4 Negation of truth and implication with constants

**Statements.**

$$
\vdash\neg\top\leftrightarrow\bot,\qquad
(\vdash\neg\top)\Longleftrightarrow(\vdash\bot).
$$

For every $p$,

$$
\vdash p\to\top,\qquad
(\vdash p\to\bot)\Longleftrightarrow(\vdash\neg p),
$$

$$
(\vdash\top\to p)\Longleftrightarrow(\vdash p),\qquad
\vdash\bot\to p.
$$

**Proof.** From $\neg\top$, the negation axiom gives $\top\to\bot$;
apply it to the theorem $\top$. The converse is explosion. Discharge and
combine, then use transport for the external equivalence. Of the four
implication clauses, the first adds an antecedent to $\top$; the second is
the definition of negation; the third uses MP with $\top$ in one direction
and antecedent introduction in the other; the fourth is explosion. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_not_true_th`, `MLK_not_true`, and
`MLK_imp_clauses` (the four clauses in the displayed order).

### 8.5 Equivalence from positive or negative information

**Statements.**

$$
\frac{\vdash p\qquad\vdash q}{\vdash p\leftrightarrow q},\qquad
\frac{\vdash\neg p\qquad\vdash\neg q}{\vdash p\leftrightarrow q},\qquad
\frac{\vdash\neg p}{\vdash p\to q}.
$$

**Proof.** For positive information, add antecedent $p$ to $q$ and antecedent
$q$ to $p$, then introduce the biconditional. Apply this to $\neg p,\neg q$
and use Section 7.6 to obtain the negative-information rule. For the final
rule, turn $\neg p$ into $p\to\bot$ and compose with $\bot\to q$.
$\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_proves_iff_pos`, `MLK_proves_iff_neg`,
`MLK_imp_introl`.

### 8.6 Negated disjunctions and implications

**Statements.**

$$
\frac{\vdash\neg p\qquad\vdash\neg q}{\vdash\neg(p\lor q)},\qquad
\vdash\neg(p\to q)\leftrightarrow(p\land\neg q),\qquad
\frac{\vdash p\qquad\vdash\neg q}{\vdash\neg(p\to q)}.
$$

**Proof.** Conjoin the two negations and apply De Morgan for the first rule.
For the internal equivalence, assume $\neg(p\to q)$. If $\neg p$ held,
Section 8.5 would give $p\to q$, a contradiction; double-negation elimination
therefore gives $p$. Also $q\to(p\to q)$, so contraposition gives $\neg q$.
Conjoin these conclusions. Conversely, from $p\land\neg q$, assuming
$p\to q$ gives $q$ and hence $\bot$; discharge to obtain $\neg(p\to q)$.
DT and biconditional introduction complete the equivalence. The last rule
conjoins its premises and uses this equivalence. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_proves_not_or`, `MLK_crysippus_th`,
`MLK_proves_not_imp`.

### 8.7 Combining equivalent conclusions and comparison with truth

**Statements.**

$$
\frac{\vdash p\leftrightarrow q\qquad\vdash p\leftrightarrow q'}
{\vdash p\leftrightarrow(q\land q')},
$$

$$
\vdash(p\leftrightarrow\top)\leftrightarrow p,\qquad
\vdash(\top\leftrightarrow p)\leftrightarrow p.
$$

**Proof.** Combine the forward implications from $p$ using conjunction
introduction under a common antecedent. For the reverse implication, project
$q$ and apply $q\to p$. For comparison with truth, extract $\top\to p$
from the assumed biconditional and apply it to $\top$. Conversely, under
$p$, antecedent introduction gives $\top\to p$, while $p\to\top$ is
always derivable. Introduce the biconditional; symmetry handles its other
order. Discharge and combine the directions of each identity. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_imp_th`, `MLK_iff_true_th`
(the latter packages both displayed identities).

### 8.8 Reasoning from true or false implications

**Statements.**

$$
\vdash(q\to\bot)\to(p\to((p\to q)\to\bot)),
$$

$$
\frac{\vdash(p\to\bot)\to r\qquad\vdash q\to r}{\vdash(p\to q)\to r},
\qquad
\frac{\vdash(q\to\bot)\to(p\to r)}{\vdash((p\to q)\to\bot)\to r}.
$$

**Comment.** These rules expose the classical cases that make an implication
true or false and are useful for subsequent case-based arguments.

**Proof.** For the first formula, assume $q\to\bot$, $p$, and $p\to q$.
Two MP steps give $\bot$; discharge in reverse order. For the second, assume
$p\to q$ and use Boolean cases on $p$. If $p$, derive $q$ and then $r$;
if $p\to\bot$, the other premise gives $r$. Discharge the implication.

For the last rule, assume $(p\to q)\to\bot$. Use Boolean cases on $q$.
If $q$, antecedent introduction gives $p\to q$, hence a contradiction and
$r$. Otherwise $q\to\bot$, so the premise gives $p\to r$. Split on $p$:
if $p$, derive $r$; otherwise $p\to\bot$, so explosion gives $p\to q$,
again a contradiction and $r$. Discharge the initial assumption. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_truefalse_th`,
`MLK_imp_true_rule`, `MLK_imp_false_rule`.

## 9. Distributivity

### 9.1 Distributing a common conjunct over a disjunction

**Statement.**

$$
(\vdash(p\lor q)\land r)\Longleftrightarrow
(\vdash(p\land r)\lor(q\land r)).
$$

**Proof.** In the forward direction, project $p\lor q$ and $r$. Eliminate
the disjunction: the $p$ branch constructs $p\land r$ and introduces the
left disjunct; the $q$ branch constructs $q\land r$ and introduces the
right disjunct. Conversely, eliminate $(p\land r)\lor(q\land r)$. Either
branch supplies $r$ and one of $p,q$, from which obtain $p\lor q$ and
conjoin it with $r$. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_or_and_distr` is the forward rule,
`MLK_or_and_distr_inv` the reverse rule, and `MLK_or_and_distr_equiv` their
external equivalence.

### 9.2 Distributing a common disjunct over a conjunction

**Statement.**

$$
(\vdash(p\land q)\lor r)\Longleftrightarrow
(\vdash(p\lor r)\land(q\lor r)).
$$

An intermediate rule used for the reverse direction is

$$
\frac{\vdash(p\lor r)\land(q\lor r)}{\vdash q\to((p\land q)\lor r)}.
$$

**Proof.** For the forward direction, eliminate $(p\land q)\lor r$.
From $p\land q$, its projections introduce $p\lor r$ and $q\lor r$;
from $r$, introduce it into both disjunctions. Conjoin in either branch.

For the intermediate rule, project $p\lor r$ and assume $q$. In the $p$
branch form $p\land q$ and introduce the left target disjunct; in the $r$
branch introduce the right one. Discharge $q$. For the full reverse rule,
project $q\lor r$ and eliminate it: the $q$ branch uses the intermediate
rule, and the $r$ branch introduces $r$ directly. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_or_distr`,
`MLK_and_or_distr_inv`, `MLK_and_or_distr_equiv` name the forward rule,
reverse rule, and external equivalence; `MLK_and_or_distr_inv_prelim` is the
intermediate rule.

### 9.3 Internal left distributivity

**Statement.**

$$
\vdash(p\land(q\lor r))\leftrightarrow((p\land q)\lor(p\land r)).
$$

**Proof.** Assume $p\land(q\lor r)$. Project $p$ and $q\lor r$, then
eliminate the disjunction: construct $p\land q$ or $p\land r$ and
introduce the corresponding target disjunct. Conversely, from either
$p\land q$ or $p\land r$, keep $p$ and introduce $q\lor r$ using the
other conjunct, then conjoin. Disjunction elimination completes this
direction. DT and biconditional introduction give the internal equivalence.
$\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_and_or_ldistrib_th`.

## 10. Modal consequences

Here we write contexts explicitly whenever a premise must have no local
hypotheses. All other judgments share the fixed $S,H$ convention of Section 1.

### 10.1 Monotonicity of necessity and boxed modus ponens

**Statements.**

$$
\frac{S;\varnothing\vdash p\to q}{S;H\vdash\Box p\to\Box q},
$$

$$
\frac{\vdash\Box(p\to q)}{\vdash\Box p\to\Box q},\qquad
\frac{\vdash\Box(p\to q)\qquad\vdash\Box p}{\vdash\Box q},
$$

$$
\frac{S;\varnothing\vdash p\to q\qquad S;H\vdash\Box p}
{S;H\vdash\Box q}.
$$

**Comment.** The empty context is needed when a new box is introduced by
necessitation. An already boxed implication can be used under local hypotheses.

**Proof.** For monotonicity, necessitate the empty-context premise and apply
MP with K. For the second rule, its boxed premise is already available, so
apply K directly. Another MP step with $\Box p$ gives boxed modus ponens.
For the last rule, apply monotonicity to the empty-context implication and
then MP to $\Box p$. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_imp_box`, `MLK_boximp`, and
`MLK_box_moduspones` name the first, second, and fourth rules.
The third is `MLK_box_modusponens` in Lean; there is no same-named theorem
in this HOL Light file, where it follows from `MLK_boximp` and
`MLK_modusponens`. The two historical spellings name different premises.

### 10.2 Congruence under necessity

**Statements.**

$$
\vdash\Box(p\leftrightarrow q)\to(\Box p\leftrightarrow\Box q),\qquad
\frac{\vdash\Box(p\leftrightarrow q)}{\vdash\Box p\leftrightarrow\Box q},
$$

$$
\frac{S;\varnothing\vdash p\leftrightarrow q}
{S;H\vdash\Box p\leftrightarrow\Box q}.
$$

**Proof.** The projection formulas
$(p\leftrightarrow q)\to(p\to q)$ and
$(p\leftrightarrow q)\to(q\to p)$ are theorems in the empty context.
Necessity monotonicity therefore turns them into implications from
$\Box(p\leftrightarrow q)$ to $\Box(p\to q)$ and $\Box(q\to p)$.
Under the boxed-biconditional assumption, MP and K yield
$\Box p\to\Box q$ and $\Box q\to\Box p$. Combine them and discharge
that assumption for the first statement. MP gives the second. For the
third, necessitate the empty-context equivalence and use the second rule.
$\square$

**Comment.** The argument boxes the empty-context projection theorems, not
implications extracted under a local assumption. An arbitrary locally
proved equivalence does not justify replacement under $\Box$.

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_box_iff_th`, `MLK_box_iff`,
`MLK_box_subst`.

### 10.3 Necessity preserves conjunction

**Statements.**

$$
\frac{\vdash\Box(p\land q)}{\vdash\Box p\land\Box q},\qquad
\frac{\vdash\Box p\land\Box q}{\vdash\Box(p\land q)},
$$

$$
\vdash\Box(p\land q)\to(\Box p\land\Box q),\qquad
\vdash(\Box p\land\Box q)\to\Box(p\land q).
$$

Consequently,

$$
\vdash\Box(p\land q)\leftrightarrow(\Box p\land\Box q).
$$

**Proof.** Apply necessity monotonicity to the empty-context projection
theorems $(p\land q)\to p$ and $(p\land q)\to q$. The premise
$\Box(p\land q)$ then gives $\Box p,\Box q$ by MP; conjoin them.
Conversely, necessitate the empty-context theorem
$p\to(q\to(p\land q))$. Project $\Box p,\Box q$ from the premise.
Apply boxed MP twice to obtain $\Box(p\land q)$. DT gives the two internal
implications, and biconditional introduction gives the consequence.
$\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_box_and`, `MLK_box_and_inv`,
`MLK_box_and_th`, `MLK_box_and_inv_th`, respectively. The final biconditional
is a consequence of these declarations, not a separately named theorem here.

### 10.4 Possibility and conjunction

**Statement.**

$$
\vdash\Diamond(p\land q)\to(\Diamond p\land\Diamond q).
$$

**Proof.** In the empty context, contrapose each conjunction projection to
obtain $\neg p\to\neg(p\land q)$ and
$\neg q\to\neg(p\land q)$. Necessity monotonicity gives
$\Box\neg p\to\Box\neg(p\land q)$ and its analogue for $q$.
Contrapose once more and unfold $\Diamond$ to obtain
$\Diamond(p\land q)\to\Diamond p$ and
$\Diamond(p\land q)\to\Diamond q$. Conjoin these consequences under their
common antecedent. $\square$

**Comment.** The converse is not a general K principle. For intuition, take
a world with two accessible terminal successors: let only $p$ hold at the
first and only $q$ at the second. Both $\Diamond p$ and $\Diamond q$ hold
at the original world, but $\Diamond(p\land q)$ does not. This semantic
observation is separate from the syntactic proof above.

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `MLK_diam_and_th`.

## 11. Uniform substitution

A substitution $\sigma$ assigns a formula to each atom and extends to all
formulas by

$$
\sigma(\bot)=\bot,\quad\sigma(\top)=\top,\quad
\sigma(a)=\sigma_a,\quad
\sigma(\neg p)=\neg\sigma(p),\quad
\sigma(\Box p)=\Box\sigma(p),
$$

$$
\sigma(p\circ q)=\sigma(p)\circ\sigma(q)
\qquad(\circ\in\{\land,\lor,\to,\leftrightarrow\}).
$$

Here $\sigma_a$ denotes the formula assigned to atom $a$. For a set $X$ of
formulas, put $\sigma[X]=\{\sigma(p):p\in X\}$. These equations express
uniform replacement at every occurrence of each atom.

**Formalization references.** [HOL Light](../calculus.ml): `SUBST`.
[Lean](../lean/HOLMS/Calculus.lean): `Form.subst`, with compatibility
abbreviation `SUBST`. Its nine equations are also provided as
`Form.subst_falsum`, `Form.subst_verum`, `Form.subst_atom`, `Form.subst_neg`,
`Form.subst_conj`, `Form.subst_disj`, `Form.subst_imp`, `Form.subst_iff`,
`Form.subst_box`; their proofs unfold the corresponding defining clause.

### 11.1 Primitive axioms are substitution-invariant

**Statement.** For every substitution $\sigma$ and formula $p$,

$$
p\in\mathsf{Ax}_K\Longrightarrow\sigma(p)\in\mathsf{Ax}_K.
$$

**Proof.** Inspect which of the eleven schemata produces $p$. Substitution
preserves every constructor and constant in that schema; replacing its
formula parameters by their substituted versions therefore yields another
instance of the same schema. For example, K becomes
$\Box(\sigma(p)\to\sigma(q))\to(\Box\sigma(p)\to\Box\sigma(q))$.
The same argument applies to each propositional schema. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `KAXIOM_SUBST`.

### 11.2 Substitution transports derivations

**Statement.** Suppose $\sigma[S]\subseteq S$. Then

$$
S;H\vdash p\Longrightarrow S;\sigma[H]\vdash\sigma(p).
$$

**Comment.** The extra axiom set stays fixed, so its closure under this
particular substitution is an explicit hypothesis. An arbitrary set $S$
need not have this property.

**Proof.** Fix $S,\sigma$ and induct on the derivation, allowing the local
context and conclusion to vary. A primitive K axiom is preserved by
Section 11.1. An additional axiom remains in $S$ by the closure hypothesis.
A local hypothesis $a\in H$ becomes $\sigma(a)\in\sigma[H]$. For MP,
substitution commutes with implication, so MP applied to the two induction
hypotheses gives the substituted conclusion. Finally, a necessitation step
starts from $S;\varnothing\vdash a$. Its induction hypothesis has context
$\sigma[\varnothing]=\varnothing$, so necessitation applies to
$\sigma(a)$ and gives $\Box\sigma(a)=\sigma(\Box a)$ in the desired
context. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `SUBST_IMP`.

### 11.3 Uniform substitution in a derivable equivalence

**Statement.** If $\sigma[S]\subseteq S$, then

$$
S;H\vdash p\leftrightarrow q\Longrightarrow
S;\sigma[H]\vdash\sigma(p)\leftrightarrow\sigma(q).
$$

**Proof.** Apply Section 11.2 to $p\leftrightarrow q$, and use the defining
equation for substitution through a biconditional. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `SUBSTITUTION_LEMMA`.

### 11.4 Pointwise equivalent substitutions

**Statement.** Let $\sigma,\tau$ be substitutions such that

$$
\forall a,\quad S;\varnothing\vdash\sigma_a\leftrightarrow\tau_a.
$$

Then for every formula $p$ and every local context $H$,

$$
S;H\vdash\sigma(p)\leftrightarrow\tau(p).
$$

**Comment.** This compares the results of two substitutions, rather than
substituting into a derivation. It requires no substitution-closure hypothesis
on $S$. The pointwise equivalences must be theorems without local hypotheses
because atoms may occur inside boxes.

**Proof.** Induct on the structure of $p$, with the conclusion quantified
over **all contexts $H$**. Constants use biconditional reflexivity. At an
atom, weaken the assumed empty-context equivalence to $H$. Negation and
the binary propositional connectives use their congruence rules with the
induction hypotheses in $H$.

For $p=\Box r$, instantiate the induction hypothesis for $r$ at the empty
context. It gives $S;\varnothing\vdash\sigma(r)\leftrightarrow\tau(r)$.
Modal congruence (Section 10.2) then yields
$S;H\vdash\Box\sigma(r)\leftrightarrow\Box\tau(r)$, which is the required
statement by the substitution equations. The generalization over $H$ is
what makes this empty-context use legitimate. $\square$

**Formalization references.** [HOL Light](../calculus.ml) and
[Lean](../lean/HOLMS/Calculus.lean): `SUBST_IFF`.

## 12. Role in the wider development

The calculus separates global axioms from dischargeable local hypotheses,
reconstructs classical propositional reasoning, and supplies the modal rules
that follow from K and restricted necessitation. Uniform substitution and
congruence make these results reusable across formulas and axiom systems.
This syntactic infrastructure supports later soundness, completeness,
decidability, and countermodel constructions for particular modal logics.
