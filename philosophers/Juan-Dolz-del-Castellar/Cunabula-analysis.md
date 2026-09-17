# Analysis of Dolz, *Cunabula omnium fere scientiarum* (1518)

A running commentary on Juan Dolz del Castellar, *Cunabula omnium fere scientiarum et praecipue
physicalium difficultatum in proportionibus et proportionalitatibus* (Montalbanum, 1518), following
the text page by page. Sections are added as the transcription advances; page references are to the
folio numbers of the transcription.

---

# Preambles 1–8: number, the aliquot part, and the non-aliquot part

**Pages 25a–27b.** The eight preambles that precede the definitions of the first article, with
particular attention to the definitions of *pars aliquota* and *pars non aliquota*.

## 1. Why the metaphysics comes first

The definitions of preambles 6–8 are unintelligible without the scaffolding laid down in
preambles 1–4. Dolz builds that scaffolding deliberately, and he warns the reader what kind of
scaffolding it is.

**Preamble 1 (25a–25b).** In treating numbers, quantities, proportions and proportionalities he
will speak *more Realium* — with the Realists — "licet opinio Nominalium in his verior sit",
although the Nominalist opinion is truer. The justification is methodological: this science is
handed down *via doctrinae*, and "quidpiam imaginari solemus ut quod quaerimus enucleemus, quod
tamen non est verum". He compares the device to the theologians' practice of secluding God by a
possible or impossible supposition in order to display some truth. The entire apparatus that
follows is therefore an avowed *imaginatio*, adopted for brevity and clarity, not a thesis.

**Preambles 2–3 (25b–26a).** The mathematicians, with the Realists, posit numbers as
**indivisible**. Dolz distinguishes:

- *numerus transcendentalis* — the enumerated things themselves;
- *numerus praedicamentalis* — an accident, distinct from the enumerated things and indivisible,
  inhering in them **copulatim**, jointly.

The same distinction applies to unity. Hence the *binarius praedicamentalis* is "accidens quoddam
indivisibile duabus rebus copulatim inhaerens". Predicamental number divides into binary, ternary,
quaternary and so on without end; predicamental unity admits no further division into species.

**Preamble 4 (26a–26b).** An obvious objection follows: if numbers are indivisible, how can one
number be greater than another? Not, says Dolz, because it is composed of more unities, "cum non
componatur indivisibile". His three conclusions:

1. A number is greater because it *presupposes* more unities, inheres in more, and
   **results** from more *sine compositione*.
2. A number is lesser because it presupposes fewer and results from fewer *incomponibiliter*.
3. Numbers are equal when they presuppose neither more nor fewer.

Therefore greater, lesser and equal are attributed to numbers **aliquantulum improprie** — because
"nihil alicui aio proprie attribui quod non ratione sui sed alterius convenit". Dolz then guards
the doctrine against Aristotle's dictum in the *Categories* that equal and unequal are most proper
to quantity, and notes that Gaspar Lax favours him in the first book of his *Arithmetica*.

Two consequences govern everything that follows.

**(a) The resultancy gloss.** When the definition of *pars aliquota* says that the part
*conficit* the whole, Dolz immediately warns: "Non intelligas conficit, id est componit, sed ad
sensum prius datum." *Conficit* must be read in the resultancy sense of preamble 4, since on his
own account an indivisible number is composed of nothing. The same caution reappears as
"componitur **sive resultat**" in preamble 7, and as the concession that a number does not
*proprie* have an aliquot part at all, "sed ad sensum superius datum de numeri resultantia".

**(b) The conventionalist principle.** Preamble 4 already states the rule that will resolve the
puzzle of preamble 8: since the basis is *voluntaria*, one may argue *problematice* on either side
"dum tamen consequenter loquaris ubi basis voluntaria est. Quid mirum si sequentia voluntaria
sint?" The *resolutio* of preamble 8 — "descriptio termini spontanea est et unaquaeque data
sustentabilis est, sed consequenter loqui opus est" — is that same rule applied to a definition.
Dolz's answer to the aliquot-part puzzle is thus not arithmetical, and not merely semantic: it is
the methodological principle he announced two pages earlier.

**Preamble 5 (26b).** Is unity a number? Following the mathematicians properly, no. Boethius
appears to say otherwise at the opening of his *Arithmetica*. Dolz resolves the conflict twice
over: either *numerus* is taken strictly, as distinguished from unity, or broadly, as including it;
or else Boethius meant only that "appellatio numeri ex unitate scaturit" — the name of number wells
up from unity — not that unity is a number.

---

## 2. Preamble 6: the definition of *pars aliquota*

> Aliquota ab aliquotiens reddere dicitur, et est illa quae aliquotiens sumpta ipsum \[totum\]
> adaequate conficit.

Formally, the relation is:

$$
\operatorname{Aliquot}(p, W) \iff \exists\, n \in \mathbb{N},\; n \ge 2,\; n\,p = W
$$

Read: *there is a whole number $n$, of at least 2, such that $p$ taken $n$ times equals $W$ exactly.*
Throughout what follows, $p$ is the candidate part, $W$ the whole, and $n$ the number of repetitions;
the condition $n \ge 2$ restricts which values of $n$ may be tried, and is not part of the equation.

The definition is **relational**, not a classification of parts into two intrinsic kinds. Nothing is
an aliquot part *simpliciter*; a part is aliquot *of a given whole*. This is the single point on
which the whole of preamble 8 turns.

Two conditions, each separately motivated in the text:

| Condition | Text | Reason |
| --- | --- | --- |
| $n \ge 2$ | "Expone bis aut ter aut quater… Non exponas semel" | If taken once it would yield the whole, not a part; and "ipsiusmet non est pars" |
| exactness | *adaequate*, glossed "non magis nec minus" | No remainder, no excess |

### The four conclusions

1. **Unity is an aliquot part of every number.** $1 \cdot n = n$ for every $n \ge 2$. This is the
   arithmetical fact that the continuum will be shown to lack.
2. **The binary is an aliquot part of every even number but itself.** The exclusion is explained:
   "Dico ipso dempto quia ipsiusmet non est pars."
3. **The ternary is not an aliquot part of every odd number** — not of $5$ — "licet bene alicuius",
   though of some, namely $9$.
4. **The binary is an aliquot part of no odd number.**

Dolz then closes by conceding that a number, being indivisible, does not *properly* have an aliquot
part at all; the whole discussion holds only *ad sensum… de numeri resultantia*.

---

## 3. The continuum passage (27a)

> Patet ultra in quantitatibus continuis non esse ut in numeris, nihil enim est quod cuiuslibet
> quantitatis continuae pars aliquota nuncupetur. Patet inductive, non pedalitas quia non
> sesquipedalitatis, nec sesquipedalitas quia non quartae, et caetera. Nihilominus continuorum pars
> aliquota est, et \[par\] non imparis est pars aliquota.

The claim is **not** that continua lack aliquot parts — Dolz denies that in the same breath. It is
that the continuum has **no analogue of the unit**. In number, unity is an aliquot part of *every*
number; among continuous magnitudes there is nothing that is an aliquot part of every magnitude.

The induction defeats each candidate by producing a whole it fails to measure:

$$
n \cdot (1\ \text{ft}) \neq 1\tfrac{1}{2}\ \text{ft}
\qquad\text{and}\qquad
n \cdot \left(1\tfrac{1}{2}\ \text{ft}\right) \neq 4\ \text{ft}
$$

for every integer $n$. The example is well chosen rather than arbitrary: $1\tfrac12$ *is* an aliquot
part of $3$ and of $4\tfrac12$, so the counter-whole has to be selected with care.

**On *quartae*.** The reading is insecure. The natural sense of *quarta* is "a fourth part", but
that cannot be right here: a part must be less than its whole (Dolz's own "ipsiusmet non est pars"),
so the counter-whole must *exceed* $1\tfrac12$ feet. The word is therefore best taken as *quartae
\[pedalitatis\]*, the fourth foot-quantity, i.e. four feet.

**On the closing clause.** As printed, *impar non imparis est pars aliquota* — "an odd is not an
aliquot part of an odd" — is false, and contradicts the third conclusion, where $3$ *is* an aliquot
part of $9$. Read *par non imparis*: no even number measures an odd one. This is the general theorem
of which the fourth conclusion (*binarius non imparis*) is the special case, and the abbreviation
*pār* / *impār* is exactly the kind of thing a compositor confuses. A weaker alternative is to
supply *cuiuslibet* from the third conclusion, which yields a truth but a redundant one.

---

## 4. Preamble 7: the division of aliquot parts (27a)

Aliquot parts are divided by the **number of repetitions** required, and are named accordingly:
*medietas sive secunda* (taken twice), the third (thrice), the fourth (four times), and so on. This
naming principle is what will generate the vocabulary of proportions — *subdupla*, *subtripla* — at
which the treatise is aiming.

$$
W = 2\left(\tfrac{W}{2}\right) = 3\left(\tfrac{W}{3}\right) = 4\left(\tfrac{W}{4}\right) = \cdots
$$

Hence "unum totum plures, immo infinitas partes aliquotas habere censetur".

**A necessary qualification.** The claims that every whole *contains* a half, a third and a fourth,
and that it has *infinitely many* aliquot parts, hold only of **continuous magnitude**. Five has no
half; and on Dolz's own account a number is indivisible and has aliquot parts only in the resultancy
sense. It is not accidental that preamble 6 shifts to continua immediately before preamble 7
introduces this division: the division presupposes a domain in which every divisor exists.

### The *discrimen*: the half is the greatest proper aliquot part

> Nam si cum medietate quidquid ultra suscipias, totius non est pars aliquota cuius est medietas,
> secus alterius; sed si cum tertia et quarta et caeteris quidquid ultra accipias, pars aliquota
> ipsius totius remanet, saltem poterit ita esse.

- Anything **exceeding $W/2$** cannot be an aliquot part of $W$: doubling it already overshoots.
  It may, however, be an aliquot part of some *other* whole — *secus alterius*.
- Anything **exceeding $W/3$ or $W/4$** may still be an aliquot part of the same $W$ — for instance
  $W/2$ itself. Hence the careful *saltem poterit ita esse*: it *can* be so, not that it must.
  Something like $0.4\,W$ exceeds $W/3$ and is an aliquot part of nothing.

The proof clause, *patet quoniam medietas est \[ultra\] tertiam et quartam et quidquid ultra*, is
defective as printed. The sense required is that the half **lies beyond** the third and the fourth:
the half is itself an instance of "something beyond a third", and it is an aliquot part. The missing
word is most likely the preposition *ultra* governing accusatives, the idiom Dolz has just used
twice in the same sentence.

The conclusion — "medietatem debere sumi bis, tertiam ter, quartam quater, et sic de singulis ad
totius resultantiam" — restates the naming principle and, once again, preserves *resultantia*
rather than composition.

Dolz then breaks off. Further properties belong to the arithmetician, and he will not exceed the
limits he set himself: the arts course at Paris is short, students attend philosophy scarcely once
a day and hardly more than a year, and masters of arts are poor — "Artes mendicant et non nisi
paleae colliguntur".

---

## 5. Preamble 8: *pars non aliquota* (27b)

Dolz notes that no preamble is commonly made on this point, but raises the difficulty anyway. Two
descriptions are canvassed, and they differ only in the **scope of the negation** relative to a
quantifier over wholes that the Latin leaves unexpressed.

The Latin says only *totum*, "the whole", without saying which whole or whether any whole will do.
Everything below turns on that silence. In the formulas, $\exists W$ renders "there is some whole such
that", and the brackets mark how far each negation reaches.

### First description — negation outside

> Pars non aliquota est quae, non aliquotiens sumpta, ipsum totum conficit adaequate.

$$
\operatorname{NonAliquot}_{1}(p) \iff \neg\;\exists W \;\exists\, n \,\big[\, n \ge 2 \;\wedge\; n\,p = W \,\big]
$$

The negation stands **outside** both quantifiers, so the demand is: *there is no whole whatsoever
that $p$ measures exactly.*

Dolz's objection: the binary is then *not* a non-aliquot part, "quia falsum quod non aliquotiens
ipsum totum conficiat adaequate; immo quaternarium aliquotiens conficit adaequate" — it does make
the quaternary exactly. Yet it plainly ought to be called a non-aliquot part, since it is a
non-aliquot part of the ternary.

The description is in fact **vacuous — nothing at all satisfies it**. For any $p$ whatever, $2p$ is a
whole that $p$ measures exactly, so the inner claim is always true and its negation always false:

$$p = 3 \Rightarrow W = 6; \qquad p = 7 \Rightarrow W = 14; \qquad p = 1\tfrac12\ \text{ft} \Rightarrow W = 3\ \text{ft}$$

Dolz says only *vix illo modo non aliquotam reperies* — you will scarcely find one — which
understates the collapse.

### Second description — negation inside

> Pars non aliquota est quae aliquotiens sumpta, aliquod totum non conficit adaequate.

$$
\operatorname{NonAliquot}_{2}(p) \iff \exists W \;\neg\;\exists\, n \,\big[\, n \ge 2 \;\wedge\; n\,p = W \,\big]
$$

The negation now stands **inside** the quantifier over wholes, so the demand is much weaker: *there
is at least one whole that $p$ fails to measure exactly.*

Worked through for $p = 2$: one chooses a candidate $W$, then runs through the permitted values of
$n$, namely $2, 3, 4, \dots$

| Candidate $W$ | Is there an $n \ge 2$ with $n \times 2 = W$? | Witness? |
| --- | --- | --- |
| $4$ | yes, $n = 2$ | no |
| $6$ | yes, $n = 3$ | no |
| $3$ | $4, 6, 8, \dots$ — never $3$ | **yes** |
| $5$ | never | **yes** |
| $2$ | would need $n = 1$, excluded | **yes** |

Only one witness is required, and $W = 3$ already supplies it. So the binary comes out non-aliquot —
while remaining aliquot with respect to $4$ and $6$. Hence "eadem est pars aliquota et non aliquota",
the same part is both.

Dolz's own example is the binary, which is aliquot "ut constat", and also non-aliquot, "nam aliquod
totum aliquotiens non conficit adaequate, puta binarium" — the whole he selects is the binary
itself, since no $n \ge 2$ gives $n \times 2 = 2$.

That choice repays attention on two counts. First, strictly nothing is a part of itself, so the
binary is not a *part* of the binary at all; Dolz nevertheless uses the phrase, and in the
*resolutio* speaks of "non aliquota binarii aut quinarii". He is treating *non aliquota N* as a bare
**relational predicate**, detached from strict parthood — which is precisely the point at issue.
Second, $W = p$ is the one witness **guaranteed to exist for every $p$ whatever**, since $n\,p = p$
would require the excluded $n = 1$. Choosing it proves the point in full generality rather than for
a lucky pair like $2$ and $3$.

### The two descriptions are defective in opposite directions

The symmetry is worth stating plainly, since it is the real result of the preamble:

| | Condition | Extension |
| --- | --- | --- |
| $\operatorname{NonAliquot}_{1}$ | fails for **every** whole | **empty** — witness $W = 2p$ always defeats it |
| $\operatorname{NonAliquot}_{2}$ | fails for **some** whole | **universal** — witness $W = p$ always satisfies it |

One description is too strong and catches nothing; the other is too weak and catches everything.
Neither divides parts into two groups, which is exactly why the only usable form is the two-place
relation $\operatorname{Aliquot}(p, W)$, with the whole named.

### The *resolutio*

Three moves, in order:

**1. Either description may be held, provided one speaks consistently.** "Descriptio termini
spontanea est et unaquaeque data sustentabilis est, sed consequenter loqui opus est." The
description of a term is free; what is not free is the inferential behaviour that follows from it.

**2. On the first description, one inference must be denied:**

> est non aliquota binarii; ergo est non aliquota

This is a textbook ***a secundum quid ad simpliciter*** fallacy — passing from a relational
predication to an absolute one. Dolz does not name it, but that is the diagnosis, and it is exactly
where the *logicus* and the *mathematicus* part company: "Consequentiam concederet mathematicus,
quidquid diceret logicus."

The appeal to *obligationes* that follows is a real argumentative move, not ornament. The
mathematician would not adopt the first description, "quia non staret in rigore illius
descriptionis"; but under *positio* he would be bound to accept it, by the famous rule of the art of
obligations that any term may be made convertible with any other by a new imposition.

**3. On the second description, the apparent contradiction is not one.** Dolz concedes outright
that the same part is aliquot and non-aliquot simultaneously, and observes that this "consonat
mathematicis". The defence: "nec illi termini contradictorie caperentur, quia, ut vides,
descriptiones non opponerentur." The prefixed *non* is not a contradictory-forming negation; it is
part of a complex term carrying its own stipulated description, exactly as the dialecticians treat
*conceptus ultimatus* and *non ultimatus*. Since "fails to measure some whole" and "measures some
other whole" are not contradictory opposites, conceding both violates no principle.

The final clause — "ibi praesupponimus, quantum ad quantitatem, idem esse quod distinguantur aut
non, in lectura philosophiae aperuimus" — is corrupt beyond confident repair. It appears to defer a
question about whether the two descriptions differ *quantum ad quantitatem* to his philosophy
lectures.

---

## 6. Summary of the doctrine

1. *Aliquot part* is a **two-place relation** between a part and a whole, requiring exact measure
   and at least two repetitions.
2. Dropping the second term of the relation is what generates every difficulty in preamble 8.
3. Number and continuum behave differently: number has a universal aliquot part, unity; the
   continuum has none, though every continuous whole has infinitely many aliquot parts.
4. The half is the greatest proper aliquot part of any whole.
5. *Non aliquot part* admits two consistent but non-equivalent descriptions, differing in
   quantifier scope. The first has an empty extension, the second a universal one; the second,
   which matches mathematical usage, makes *aliquot* and *non aliquot* compatible without
   contradiction.
6. The resolution is conventionalist and continuous with preamble 4: where the basis of a science
   is voluntary, descriptions are free and only consistency binds.

---

## 7. Textual notes

Proposed emendations arising from the analysis. Those marked *insecure* are recorded but not
recommended for adoption.

| Page | Printed | Proposed | Ground |
| --- | --- | --- | --- |
| 26b | Binarius cuiuslibet **partis** | **paris** | "ipso dempto… ipsiusmet non est pars" presupposes that the binary is itself among the wholes in question, i.e. the evens |
| 26b | ipsum adaequate conficit **aliquotiens** | delete | Dittography from the preceding *aliquotiens sumpta* |
| 26b | ipsum adaequate conficit | ipsum **totum** adaequate conficit | *totum* supplied from the citations of the definition in preamble 8 |
| 27a | cum **situs** sit indivisibilis | cum **ipse** sit indivisibilis | *situs* is unmotivated; the indivisible in question is the number, per preambles 2–3 |
| 27a | et **impar** non imparis | **par** non imparis | As printed the clause is false and contradicts the third conclusion |
| 27a | medietas est tertia et quarta | medietas est **ultra** tertiam et quartam | Required sense; matches the *quidquid ultra* idiom used twice in the same sentence |
| 27a | nec sesquipedalitas quia non **quartae** | *(insecure)* | Taken as *quartae \[pedalitatis\]*, four feet; "a fourth part" is arithmetically inapt, since a part must be less than its whole |
| 27b | ibi praesupponimus… aut non | *(corrupt; left as printed)* | Beyond confident repair |
