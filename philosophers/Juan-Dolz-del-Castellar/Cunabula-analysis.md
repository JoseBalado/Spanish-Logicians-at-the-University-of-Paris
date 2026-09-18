# Analysis of Dolz, _Cunabula omnium fere scientiarum_ (1518)

A running commentary on Juan Dolz del Castellar, _Cunabula omnium fere scientiarum et praecipue physicalium difficultatum in proportionibus et proportionalitatibus_ (Montalbanum, 1518), following the text page by page. Sections are added as the transcription advances; page references are to the folio numbers of the transcription.

---

# Preambles 1–9: number, the aliquot part, and proportion

**Pages 25a–28b.** The nine preambles that precede the definitions of the first article, with particular attention to _pars aliquota_, _pars non aliquota_, and the opening definition of proportion.

## 1. Why the metaphysics comes first

The definitions of preambles 6–8 are unintelligible without the scaffolding laid down in preambles 1–4. Dolz builds that scaffolding deliberately, and he warns the reader what kind of scaffolding it is.

**Preamble 1 (25a–25b).** In treating numbers, quantities, proportions and proportionalities he will speak _more Realium_ — with the Realists — "licet opinio Nominalium in his verior sit", although the Nominalist opinion is truer. The justification is methodological: this science is handed down _via doctrinae_, and "quidpiam imaginari solemus ut quod quaerimus enucleemus, quod tamen non est verum". He compares the device to the theologians' practice of secluding God by a possible or impossible supposition in order to display some truth. The entire apparatus that follows is therefore an avowed _imaginatio_, adopted for brevity and clarity, not a thesis.

**Preambles 2–3 (25b–26a).** The mathematicians, with the Realists, posit numbers as **indivisible**. Dolz distinguishes:

- _numerus transcendentalis_ — the enumerated things themselves;
- _numerus praedicamentalis_ — an accident, distinct from the enumerated things and indivisible, inhering in them **copulatim**, jointly.

The same distinction applies to unity. Hence the _binarius praedicamentalis_ is "accidens quoddam indivisibile duabus rebus copulatim inhaerens". Predicamental number divides into binary, ternary, quaternary and so on without end; predicamental unity admits no further division into species.

**Preamble 4 (26a–26b).** An obvious objection follows: if numbers are indivisible, how can one number be greater than another? Not, says Dolz, because it is composed of more unities, "cum non componatur indivisibile". His three conclusions:

1. A number is greater because it _presupposes_ more unities, inheres in more, and **results** from more _sine compositione_.
2. A number is lesser because it presupposes fewer and results from fewer _incomponibiliter_.
3. Numbers are equal when they presuppose neither more nor fewer.

Therefore greater, lesser and equal are attributed to numbers **aliquantulum improprie** — because "nihil alicui aio proprie attribui quod non ratione sui sed alterius convenit". Dolz then guards the doctrine against Aristotle's dictum in the _Categories_ that equal and unequal are most proper to quantity, and notes that Gaspar Lax favours him in the first book of his _Arithmetica_.

Two consequences govern everything that follows.

**(a) The resultancy gloss.** When the definition of _pars aliquota_ says that the part _conficit_ the whole, Dolz immediately warns: "Non intelligas conficit, id est componit, sed ad sensum prius datum." _Conficit_ must be read in the resultancy sense of preamble 4, since on his own account an indivisible number is composed of nothing. The same caution reappears as "componitur **sive resultat**" in preamble 7, and as the concession that a number does not _proprie_ have an aliquot part at all, "sed ad sensum superius datum de numeri resultantia".

**(b) The conventionalist principle.** Preamble 4 already states the rule that will resolve the puzzle of preamble 8: since the basis is _voluntaria_, one may argue _problematice_ on either side "dum tamen consequenter loquaris ubi basis voluntaria est. Quid mirum si sequentia voluntaria sint?" The _resolutio_ of preamble 8 — "descriptio termini spontanea est et unaquaeque data sustentabilis est, sed consequenter loqui opus est" — is that same rule applied to a definition. Dolz's answer to the aliquot-part puzzle is thus not arithmetical, and not merely semantic: it is the methodological principle he announced two pages earlier.

**Preamble 5 (26b).** Is unity a number? Following the mathematicians properly, no. Boethius appears to say otherwise at the opening of his _Arithmetica_. Dolz resolves the conflict twice over: either _numerus_ is taken strictly, as distinguished from unity, or broadly, as including it; or else Boethius meant only that "appellatio numeri ex unitate scaturit" — the name of number wells up from unity — not that unity is a number.

---

## 2. Preamble 6: the definition of _pars aliquota_

> Aliquota ab aliquotiens reddere dicitur, et est illa quae aliquotiens sumpta ipsum \[totum\] adaequate conficit.

In Lean 4, the relation is:

```lean
import Init

def Aliquot (p W : Nat) : Prop :=
   ∃ n : Nat, 2 ≤ n ∧ n * p = W
```

Read: _there is a whole number $n$, of at least 2, such that $p$ taken $n$ times equals $W$ exactly._ Throughout what follows, $p$ is the candidate part, $W$ the whole, and $n$ the number of repetitions; the condition $n \ge 2$ restricts which values of $n$ may be tried, and is not part of the equation. Lean's `Nat` includes zero, but Dolz's parts and magnitudes are implicitly positive. Claims below that quantify over every part therefore assume `0 < p`; in particular, `NonAliquot₂ 0` is false.

The definition is **relational**, not a classification of parts into two intrinsic kinds. Nothing is an aliquot part _simpliciter_; a part is aliquot _of a given whole_. This is the single point on which the whole of preamble 8 turns.

Two conditions, each separately motivated in the text:

| Condition | Text | Reason |
| --- | --- | --- |
| $n \ge 2$ | "Expone bis aut ter aut quater… Non exponas semel" | If taken once it would yield the whole, not a part; and "ipsiusmet non est pars" |
| exactness | _adaequate_, glossed "non magis nec minus" | No remainder, no excess |

### The four conclusions

1. **Unity is an aliquot part of every number.** $1 \cdot n = n$ for every $n \ge 2$. This is the arithmetical fact that the continuum will be shown to lack.
2. **The binary is an aliquot part of every even number but itself.** The exclusion is explained: "Dico ipso dempto quia ipsiusmet non est pars."
3. **The ternary is not an aliquot part of every odd number** — not of $5$ — "licet bene alicuius", though of some, namely $9$.
4. **The binary is an aliquot part of no odd number.**

Dolz then closes by conceding that a number, being indivisible, does not _properly_ have an aliquot part at all; the whole discussion holds only _ad sensum… de numeri resultantia_.

---

## 3. The continuum passage (27a)

> Patet ultra in quantitatibus continuis non esse ut in numeris, nihil enim est quod cuiuslibet quantitatis continuae pars aliquota nuncupetur. Patet inductive, non pedalitas quia non sesquipedalitatis, nec sesquipedalitas quia non quartae, et caetera. Nihilominus continuorum pars aliquota est, et \[par\] non imparis est pars aliquota.

The claim is **not** that continua lack aliquot parts — Dolz denies that in the same breath. It is that the continuum has **no analogue of the unit**. In number, unity is an aliquot part of _every_ number; among continuous magnitudes there is nothing that is an aliquot part of every magnitude.

The induction defeats each candidate by producing a whole it fails to measure:

$$
n \cdot (1\ \text{ft}) \neq 1\tfrac{1}{2}\ \text{ft}
\qquad\text{and}\qquad
n \cdot \left(1\tfrac{1}{2}\ \text{ft}\right) \neq 4\ \text{ft}
$$

for every integer $n$. The example is well chosen rather than arbitrary: $1\tfrac12$ _is_ an aliquot part of $3$ and of $4\tfrac12$, so the counter-whole has to be selected with care.

**On _quartae_.** The reading is insecure. The natural sense of _quarta_ is "a fourth part", but that cannot be right here: a part must be less than its whole (Dolz's own "ipsiusmet non est pars"), so the counter-whole must _exceed_ $1\tfrac12$ feet. The word is therefore best taken as _quartae \[pedalitatis\]_, the fourth foot-quantity, i.e. four feet.

**On the closing clause.** As printed, _impar non imparis est pars aliquota_ — "an odd is not an aliquot part of an odd" — is false, and contradicts the third conclusion, where $3$ _is_ an aliquot part of $9$. Read _par non imparis_: no even number measures an odd one. This is the general theorem of which the fourth conclusion (_binarius non imparis_) is the special case, and the abbreviation _pār_ / _impār_ is exactly the kind of thing a compositor confuses. A weaker alternative is to supply _cuiuslibet_ from the third conclusion, which yields a truth but a redundant one.

---

## 4. Preamble 7: the division of aliquot parts (27a)

Aliquot parts are divided by the **number of repetitions** required, and are named accordingly: _medietas sive secunda_ (taken twice), the third (thrice), the fourth (four times), and so on. This naming principle is what will generate the vocabulary of proportions — _subdupla_, _subtripla_ — at which the treatise is aiming.

$$
W = 2\left(\tfrac{W}{2}\right) = 3\left(\tfrac{W}{3}\right) = 4\left(\tfrac{W}{4}\right) = \cdots
$$

Hence "unum totum plures, immo infinitas partes aliquotas habere censetur".

**A necessary qualification.** The claims that every whole _contains_ a half, a third and a fourth, and that it has _infinitely many_ aliquot parts, hold only of **continuous magnitude**. Five has no half; and on Dolz's own account a number is indivisible and has aliquot parts only in the resultancy sense. It is not accidental that preamble 6 shifts to continua immediately before preamble 7 introduces this division: the division presupposes a domain in which every divisor exists.

### The _discrimen_: the half is the greatest proper aliquot part

> Nam si cum medietate quidquid ultra suscipias, totius non est pars aliquota cuius est medietas, secus alterius; sed si cum tertia et quarta et caeteris quidquid ultra accipias, pars aliquota ipsius totius remanet, saltem poterit ita esse.

- Anything **exceeding $W/2$** cannot be an aliquot part of $W$: doubling it already overshoots. It may, however, be an aliquot part of some _other_ whole — _secus alterius_.
- Anything **exceeding $W/3$ or $W/4$** may still be an aliquot part of the same $W$ — for instance $W/2$ itself. Hence the careful _saltem poterit ita esse_: it _can_ be so, not that it must. Something like $0.4\,W$ exceeds $W/3$ and is an aliquot part of nothing.

The proof clause, _patet quoniam medietas est \[ultra\] tertiam et quartam et quidquid ultra_, is defective as printed. The sense required is that the half **lies beyond** the third and the fourth: the half is itself an instance of "something beyond a third", and it is an aliquot part. The missing word is most likely the preposition _ultra_ governing accusatives, the idiom Dolz has just used twice in the same sentence.

The conclusion — "medietatem debere sumi bis, tertiam ter, quartam quater, et sic de singulis ad totius resultantiam" — restates the naming principle and, once again, preserves _resultantia_ rather than composition.

Dolz then breaks off. Further properties belong to the arithmetician, and he will not exceed the limits he set himself: the arts course at Paris is short, students attend philosophy scarcely once a day and hardly more than a year, and masters of arts are poor — "Artes mendicant et non nisi paleae colliguntur".

---

## 5. Preamble 8: _pars non aliquota_ (27b)

Dolz notes that no preamble is commonly made on this point, but raises the difficulty anyway. Two descriptions are canvassed, and they differ only in the **scope of the negation** relative to a quantifier over wholes that the Latin leaves unexpressed.

The Latin says only _totum_, "the whole", without saying which whole or whether any whole will do. Everything below turns on that silence. In the Lean definitions, `∃ W : Nat` renders "there is some whole such that", and the indentation and parentheses mark how far each negation reaches.

### First description — negation outside

> Pars non aliquota est quae, non aliquotiens sumpta, ipsum totum conficit adaequate.

```lean
def NonAliquot₁ (p : Nat) : Prop :=
   ¬ ∃ W : Nat, ∃ n : Nat, 2 ≤ n ∧ n * p = W
```

The negation stands **outside** both quantifiers, so the demand is: _there is no whole whatsoever that $p$ measures exactly._

Dolz's objection: the binary is then _not_ a non-aliquot part, "quia falsum quod non aliquotiens ipsum totum conficiat adaequate; immo quaternarium aliquotiens conficit adaequate" — it does make the quaternary exactly. Yet it plainly ought to be called a non-aliquot part, since it is a non-aliquot part of the ternary.

The description is in fact **vacuous — nothing at all satisfies it**. For any $p$ whatever, $2p$ is a whole that $p$ measures exactly, so the inner claim is always true and its negation always false:

$$p = 3 \Rightarrow W = 6; \qquad p = 7 \Rightarrow W = 14; \qquad p = 1\tfrac12\ \text{ft} \Rightarrow W = 3\ \text{ft}$$

Dolz says only _vix illo modo non aliquotam reperies_ — you will scarcely find one — which understates the collapse.

### Second description — negation inside

> Pars non aliquota est quae aliquotiens sumpta, aliquod totum non conficit adaequate.

```lean
def NonAliquot₂ (p : Nat) : Prop :=
   ∃ W : Nat, ¬ ∃ n : Nat, 2 ≤ n ∧ n * p = W
```

The negation now stands **inside** the quantifier over wholes, so the demand is much weaker: _there is at least one whole that $p$ fails to measure exactly._

Worked through for $p = 2$: one chooses a candidate $W$, then runs through the permitted values of $n$, namely $2, 3, 4, \dots$

| Candidate $W$ | Is there an $n \ge 2$ with $n \times 2 = W$? | Witness? |
| ------------- | -------------------------------------------- | -------- |
| $4$           | yes, $n = 2$                                 | no       |
| $6$           | yes, $n = 3$                                 | no       |
| $3$           | $4, 6, 8, \dots$ — never $3$                 | **yes**  |
| $5$           | never                                        | **yes**  |
| $2$           | would need $n = 1$, excluded                 | **yes**  |

Only one witness is required, and $W = 3$ already supplies it. So the binary comes out non-aliquot — while remaining aliquot with respect to $4$ and $6$. Hence "eadem est pars aliquota et non aliquota", the same part is both.

Dolz's own example is the binary, which is aliquot "ut constat", and also non-aliquot, "nam aliquod totum aliquotiens non conficit adaequate, puta binarium" — the whole he selects is the binary itself, since no $n \ge 2$ gives $n \times 2 = 2$.

That choice repays attention on two counts. First, strictly nothing is a part of itself, so the binary is not a _part_ of the binary at all; Dolz nevertheless uses the phrase, and in the _resolutio_ speaks of "non aliquota binarii aut quinarii". He is treating _non aliquota N_ as a bare **relational predicate**, detached from strict parthood — which is precisely the point at issue. Second, $W = p$ is the one witness **guaranteed to exist for every positive $p$**, since $n\,p = p$ would require the excluded $n = 1$. Choosing it proves the point for every part in Dolz's intended domain rather than for a lucky pair like $2$ and $3$. The qualification matters in Lean because `n * 0 = 0` for every $n$.

### The two descriptions are defective in opposite directions

The symmetry is worth stating plainly, since it is the real result of the preamble:

|  | Condition | Extension |
| --- | --- | --- |
| $\operatorname{NonAliquot}_{1}$ | fails for **every** whole | **empty** — witness $W = 2p$ always defeats it |
| $\operatorname{NonAliquot}_{2}$ | fails for **some** whole | **universal for positive parts** — witness $W = p$ satisfies it |

One description is too strong and catches nothing; the other is too weak and catches everything. Neither divides parts into two groups, which is exactly why the only usable form is the two-place relation $\operatorname{Aliquot}(p, W)$, with the whole named.

### The _resolutio_

Three moves, in order:

**1. Either description may be held, provided one speaks consistently.** "Descriptio termini spontanea est et unaquaeque data sustentabilis est, sed consequenter loqui opus est." The description of a term is free; what is not free is the inferential behaviour that follows from it.

**2. On the first description, one inference must be denied:**

> est non aliquota binarii; ergo est non aliquota

This is a textbook **_a secundum quid ad simpliciter_** fallacy — passing from a relational predication to an absolute one. Dolz does not name it, but that is the diagnosis, and it is exactly where the _logicus_ and the _mathematicus_ part company: "Consequentiam concederet mathematicus, quidquid diceret logicus."

The appeal to _obligationes_ that follows is a real argumentative move, not ornament. The mathematician would not adopt the first description, "quia non staret in rigore illius descriptionis"; but under _positio_ he would be bound to accept it, by the famous rule of the art of obligations that any term may be made convertible with any other by a new imposition.

**3. On the second description, the apparent contradiction is not one.** Dolz concedes outright that the same part is aliquot and non-aliquot simultaneously, and observes that this "consonat mathematicis". The defence: "nec illi termini contradictorie caperentur, quia, ut vides, descriptiones non opponerentur." The prefixed _non_ is not a contradictory-forming negation; it is part of a complex term carrying its own stipulated description, exactly as the dialecticians treat _conceptus ultimatus_ and _non ultimatus_. Since "fails to measure some whole" and "measures some other whole" are not contradictory opposites, conceding both violates no principle.

The final clause — "ibi praesupponimus, quantum ad quantitatem, idem esse quod distinguantur aut non, in lectura philosophiae aperuimus" — is corrupt beyond confident repair. It appears to defer a question about whether the two descriptions differ _quantum ad quantitatem_ to his philosophy lectures.

---

## 6. Dullaert and preamble 9: composition of aliquot relations (28a–28b)

Page 28 opens by applying the preceding machinery to a distinction attributed to Dullaert. In numbers, every non-aliquot part can nevertheless be resolved into parts aliquot both to itself and to the relevant whole: unity supplies the common measure. Thus $2$ is non-aliquot to $3$, but both result from units. Dolz again warns that _componere_ here means _resultare_, preserving the resultancy account of predicamental number developed in preambles 2–4.

Continuous magnitudes behave differently. The side and diagonal of the same square have no common aliquot measure. Dolz takes half the diagonal as non-aliquot to the side and argues that it cannot be resolved into parts aliquot to both magnitudes. The example invokes the classical incommensurability of a square's side and diagonal and sharpens the earlier claim that continuous magnitude has no universal analogue of numerical unity.

### Aliquot is transitive

The ninth preamble states:

> Quandocumque aliquid est pars aliquota partis aliquotae alicuius, illius est pars aliquota.

In the notation already introduced, if $p$ measures $q$ exactly and $q$ measures $W$ exactly, then $p$ measures $W$ exactly. The witnesses multiply: if $n p=q$ and $m q=W$, then $(mn)p=W$. The claim can be added directly to the Lean formalization:

```lean
theorem aliquot_trans {p q W : Nat}
    (hpq : Aliquot p q) (hqw : Aliquot q W) : Aliquot p W := by
  obtain ⟨n, hn, hnp⟩ := hpq
  obtain ⟨m, hm, hmq⟩ := hqw
  refine ⟨m * n, ?_, ?_⟩
  · exact Nat.le_trans (by decide : 2 ≤ 2 * 2) (Nat.mul_le_mul hm hn)
  · rw [Nat.mul_assoc, hnp, hmq]
```

The examples with halves and thirds instantiate this multiplication of witnesses. If $p$ taken twice makes a half, it taken four times makes the whole; if taken three times makes a half, it must be taken **six**, not seven, times to make the whole. The printed _septies_ is therefore a clear error for _sexies_.

### The converses fail

Dolz immediately blocks two invalid inferences:

1. From `Aliquot p W`, it does not follow that `Aliquot p (W / 2)` or that $p$ is aliquot to another aliquot part of $W$. His example is $2$: it is aliquot to $4$, but not to $2$, the half of $4$.
2. From `Aliquot p q` and the fact that $q$ is non-aliquot to $W$, it does not follow that $p$ is non-aliquot to $W$. Unity is aliquot to $2$, while $2$ is non-aliquot to $3$, yet unity is aliquot to $3$.

Thus only the positive composition law is transitive. Non-aliquotness does not propagate either upward or downward through an aliquot relation. The following _a fortiori_ example is problematic as transcribed: "binarius est aliquotus ternarii" is false under Dolz's own definition, since no integer $n \ge 2$ satisfies $2n=3$. Because _aliquotus_ occurs nowhere else in the available text, it is not yet possible to decide whether Dolz intends a looser technical use or whether the passage is corrupt. It should not be formalized as `Aliquot 2 3` without further textual evidence. The closing warning against taking the repetitions _communicanter_ likely cautions against treating unrelated existential witnesses as though they were one shared repetition count.

---

## 7. The definition of proportion (28b)

Dolz's first definition proper is:

> Proportio sic describitur: est unius quantitatis ad alteram quantitatem certa habitudo.

A proportion is therefore a **determinate relation of one quantity to another quantity**. The frequent addition "or of one number to another number" is redundant because number is already discrete quantity. This makes proportion, like aliquot part, essentially relational rather than an intrinsic property of either term.

Dolz immediately explains _certa habitudo_ as equality or inequality **in something common to both terms**. That restriction is essential. An angel and a human are not proportioned in magnitude, because magnitude does not belong to both; they may be _non-equal_ in the merely contradictory sense, but they are not _unequal_ in the quantitative sense of one being more or less than the other. Quantitative inequality presupposes a shared measurable respect.

This definition should not yet be reduced to a Lean predicate over `Nat`. Page 28 explicitly ranges over quantity in general, including continuous magnitude, and makes common comparability part of the definition. A faithful formalization therefore needs a type of quantities together with a relation expressing a shared dimension or measure; ordinary numerical equality and order would silently discard the angel example and the distinction Dolz is making.

---

## 8. Summary of the doctrine

1. _Aliquot part_ is a **two-place relation** between a part and a whole, requiring exact measure and at least two repetitions.
2. Dropping the second term of the relation is what generates every difficulty in preamble 8.
3. Number and continuum behave differently: number has a universal aliquot part, unity; the continuum has none, though every continuous whole has infinitely many aliquot parts.
4. The half is the greatest proper aliquot part of any whole.
5. _Non aliquot part_ admits two consistent but non-equivalent descriptions, differing in quantifier scope. The first has an empty extension, the second applies to every positive part; the second, which matches mathematical usage, makes _aliquot_ and _non aliquot_ compatible without contradiction.
6. The resolution is conventionalist and continuous with preamble 4: where the basis of a science is voluntary, descriptions are free and only consistency binds.
7. The aliquot relation is transitive because its repetition counts multiply, but neither its converse nor mixed inferences involving non-aliquotness are valid.
8. Proportion is a determinate equality or inequality between quantities in a common measurable respect; mere non-equality between incomparable subjects is insufficient.

---

## 9. Textual notes

Proposed emendations arising from the analysis. Those marked _insecure_ are recorded but not recommended for adoption.

| Page | Printed | Proposed | Ground |
| --- | --- | --- | --- |
| 26b | Binarius cuiuslibet **partis** | **paris** | "ipso dempto… ipsiusmet non est pars" presupposes that the binary is itself among the wholes in question, i.e. the evens |
| 26b | ipsum adaequate conficit **aliquotiens** | delete | Dittography from the preceding _aliquotiens sumpta_ |
| 26b | ipsum adaequate conficit | ipsum **totum** adaequate conficit | _totum_ supplied from the citations of the definition in preamble 8 |
| 27a | cum **situs** sit indivisibilis | cum **ipse** sit indivisibilis | _situs_ is unmotivated; the indivisible in question is the number, per preambles 2–3 |
| 27a | et **impar** non imparis | **par** non imparis | As printed the clause is false and contradicts the third conclusion |
| 27a | medietas est tertia et quarta | medietas est **ultra** tertiam et quartam | Required sense; matches the _quidquid ultra_ idiom used twice in the same sentence |
| 27a | nec sesquipedalitas quia non **quartae** | _(insecure)_ | Taken as _quartae \[pedalitatis\]_, four feet; "a fourth part" is arithmetically inapt, since a part must be less than its whole |
| 27b | ibi praesupponimus… aut non | _(corrupt; left as printed)_ | Beyond confident repair |
| 28a | si ter sumptum reddat medietatem… **septies** | **sexies** | A half taken twice makes the whole, so a part taken three times to make the half must be taken $2 \times 3=6$ times to make the whole |
| 28b | binarius est **aliquotus ternarii** | _(insecure)_ | Contradicts the definition of _pars aliquota_; _aliquotus_ may have a different force here, or the text may be corrupt |
