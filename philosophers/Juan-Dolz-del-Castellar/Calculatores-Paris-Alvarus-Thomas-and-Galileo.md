---
title: The Paris calculatores, Alvarus Thomas, and Galileo
description: How the kinematics of the Oxford Calculators reached Paris around 1500, what Alvarus Thomas's Liber de triplici motu (1509) contains, how it compares with Galileo's Discorsi, what Duhem claimed, and where Pardo, Mair, Lax, Coronel, Celaya, Dolz, and Soto fit.
keywords: Alvarus Thomas, Liber de triplici motu, Galileo, Duhem, precursors of Galileo, Oxford Calculators, Swineshead, Heytesbury, Bradwardine, Oresme, mean speed theorem, uniformiter difformis, Domingo de Soto, Gaspar Lax, Juan Dolz, Jerónimo Pardo, John Mair, Collège de Montaigu
---

# The Paris _calculatores_, Alvarus Thomas, and Galileo

This page gathers the historical context behind Dolz's _Cunabula_ (see the [analysis](Cunabula-analysis.html)): what the Parisian authors around 1500–1530 actually knew about motion, how much of what is usually credited to Galileo is already in print in Alvarus Thomas's _Liber de triplici motu_ (Paris, 1509), what Galileo nevertheless contributed, what Pierre Duhem argued, and how the material passed between Pardo, Mair, Alvarus, Lax, Luis Coronel, Celaya, Dolz, and Soto.

References to Alvarus are to the ECHO XML transcription of the 1509 edition, by the page number of its `<pb n="…">` markers (images, not printed folios).

---

## 1. Two genres: _de proportionibus_ and _de intensione formarum_

The "calculatory" tradition contains two related but distinct kinds of treatise, and it helps to keep them apart:

| Genre | Question | Classical texts | In the Paris revival |
|---|---|---|---|
| **_De proportionibus_** | How are ratios classified, compounded, and compared? How does speed depend on the ratio of **power to resistance**? (motion _penes causam_, _Physics_ VII) | Bradwardine, _De proportionibus velocitatum in motibus_ (1328); Oresme, _De proportionibus proportionum_ | Alvarus, first part of the _Liber de triplici motu_; Lax, _Proportiones_ and _Arithmetica_ (1515); Dolz, _Cunabula_ (1518) |
| **_De intensione et remissione formarum_** | How do qualities (heat, whiteness, velocity, even charity) vary in **degree** (_gradus_) across a subject or through time? What is a uniform, uniformly difform, or difformly difform latitude? (motion _penes effectum_, _Physics_ III and VI) | Heytesbury, _Regulae solvendi sophismata_ (1335); Swineshead, _Liber calculationum_ (c. 1350); Dumbleton; Oresme, _De configurationibus qualitatum et motuum_ | Alvarus, second and later parts of the _Liber de triplici motu_; Lax, _Calculationes_; the treatise Pardo announced but never wrote |

The **mean-speed rule**, the **1 : 3 rule**, and the idea of velocity as a degree that can grow uniformly with time all belong to the second genre. Bradwardine's "velocity follows the proportion of proportions" belongs to the first. Swineshead and Alvarus combine both; Dolz's _Cunabula_ is a textbook of the first, written so that students can read the Calculators' cases of the second (_Cunabula_ 29 and 33; see sections 8 and 12 of the [analysis](Cunabula-analysis.html)).

**Is the second genre built on the first?** For teaching, yes. Mathematically, only in part.

| | _De proportionibus_ | _De intensione formarum_ |
|---|---|---|
| Mathematical tools | Classification of ratios (_multiplex_, _superparticularis_, _superpartiens_ …), composition of ratios, Bradwardine's proportion of proportions | Degrees and latitudes; uniform, uniformly difform, and difformly difform qualities; Oresme's geometric figures; sums over proportional parts (infinite series) |
| Needs the other genre? | No | Yes: every comparison of degrees, distances, and times is a ratio, and compounded ratios come up again and again (sections 2.2 and 2.6) |
| Where the questions come from | A mathematical reading of _Physics_ VII (motion _penes causam_) | The theological question of how a quality such as charity increases (commentaries on Peter Lombard, _Sentences_ I, d. 17; Scotus, Ockham), made mathematical at Oxford |
| Place in the curriculum | Taught first | Read afterwards |

The first genre prepares the reader for the second. The title of Alvarus's book announces this order (_de triplici motu **proportionibus annexis**_), and Dolz writes a textbook of proportions so that students can then read the Calculators. The second genre is not merely an application of the first, though. Its geometry of configurations and its summation of series over proportional parts are not in Bradwardine, and its questions have a separate, theological origin. Section 2.6 shows the two genres combined in a single problem.

### 1.1 Motion _penes causam_ in formulas

Write $F$ for the mover's power (_potentia_, _activitas_), $R$ for the resistance, and $v$ for the speed. Bradwardine's _De proportionibus_ (ch. 2) rejects four earlier accounts, usually summarized as follows (Crosby 1955; Clagett 1959):

| | Position | Formula | Difficulty |
|---|---|---|---|
| I | speed follows the **excess** of power over resistance | $v \propto F - R$ | $8:4$ and $4:2$ are the same ratio but give speeds $4$ and $2$ |
| II | speed follows the ratio of that excess to the resistance | $v \propto \dfrac{F-R}{R}$ | not what Aristotle says; fails for compounded ratios |
| III | speed follows the simple ratio of power to resistance (Aristotle read arithmetically) | $v \propto \dfrac{F}{R}$ | predicts motion even when $F < R$, e.g. $v \propto \tfrac12$ |
| IV | speed follows no ratio at all but a "dominance" of mover over moved | — | gives no quantitative law |

Bradwardine's own rule is that speed follows the **proportion of proportions**: speed is multiplied by $n$ when the ratio $F/R$ is raised to the power $n$,

$$
\frac{v_2}{v_1} = n \iff \frac{F_2}{R_2} = \left(\frac{F_1}{R_1}\right)^{n},
\qquad\text{equivalently}\qquad
v = k \log \frac{F}{R}.
$$

To double a speed produced by a double ratio $2:1$, the ratio must become quadruple, $4:1$, not triple. The logarithmic form also yields $v > 0$ exactly when $F > R$ and $v = 0$ when $F = R$, which removes difficulty III. This is the rule Dolz announces on page 29 (_velocitatem motus attendi penes proportionem proportionum activitatum super suas resistentias_), and the reason his students need the theory of compounded ratios before they can read _Physics_ VII.

Alvarus's example in I.1 (XML pp. 59–60), discussed in the [analysis](Cunabula-analysis.html) of page 35, separates positions I and Bradwardine: with $F:R = 8:4$ and $F:R = 4:2$ the excesses are $4$ and $2$, but the ratios are both double, so on Bradwardine's rule the two speeds are **equal**.

Lax's _Quaestiones physicales_ (1527) opens its question _de motu penes causam_ by rejecting four _erroneae positiones_. Whether they are exactly Bradwardine's four has not yet been checked.

---

## 2. What Alvarus Thomas's _Liber de triplici motu_ (1509) contains

Alvarus Thomas (Álvaro Tomás, _Ulisbonensis_) was a Portuguese master teaching at Paris. His _Liber de triplici motu proportionibus annexis_ (Paris, 1509) is the largest and most mathematical Parisian treatment of the subject in the early sixteenth century. Dolz names him among his predecessors (_si Aluarum_) and cites his _Proportiones_ II.1 and II.3 by chapter. What is known of his life is collected in section 8.

### 2.1 Velocity by its cause and by its effect

Alvarus, like his sources, measures velocity in two ways. **By its cause** (_penes causam_), it follows the ratio of the mover's power to the resistance, in Bradwardine's form. **By its effect** (_penes effectum_), it is measured by the distance traversed in a given time (p. 133):

> Velocitas motus quo ad effectum debet attendi penes spatium pertransitum: ita quod quanto spatium pertransitum fuerit maius in aequali tempore, tanto motus erit velocior. Dico tamen quod non debet attendi velocitas motus localis penes spatium corporale nec penes spatium superficiale, sed penes spatium lineale descriptum a certo puncto.

The velocity of local motion is measured by the **line** traced by a point, not by the volume or surface swept: otherwise a horse dragging a large beam would move "faster" than one dragging a small beam at the same pace.

This is Aristotle's definition of the faster in _Physics_ VI, which Alvarus cites: the faster covers more distance in equal time, or equal distance in less time. In symbols, for uniform motions,

$$
t_1 = t_2 \implies \frac{v_1}{v_2} = \frac{s_1}{s_2},
\qquad
s_1 = s_2 \implies \frac{v_1}{v_2} = \frac{t_2}{t_1}.
$$

Speed "by the effect" is thus defined only through comparisons of homogeneous magnitudes (distance with distance, time with time), never as a quotient $s/t$.

### 2.2 Distance, time, and velocity as compounded ratios

There is no velocity as "metres per second". The Euclidean theory of proportion compared only homogeneous magnitudes, so a distance could not be divided by a time. Alvarus instead states the relation among distance, time, and speed as a **composition of ratios** (p. 149):

> _Capitalis propositio._ Si velocitates sint aequales aequalibus coextensae temporibus, mobilia … aequalia spatia in eisdem temporibus absolvunt … Si vero velocitates aequales per inaequalia labantur tempora, tunc in ea proportione mobile in maiori tempore maius spatium pertransit quam in minori, in qua ipsum maius tempus se habet ad minus.

> _Secunda propositio._ Quando inaequales velocitates aequalibus temporibus coextenduntur, tunc mobile quod maiore velocitate movetur in ea proportione maius spatium pertransit quam alterum mobile, in qua se habet velocitas maior ad minorem.

> _Tertia propositio._ … tunc mobile quod movetur in maiori tempore maius spatium pertransit in proportione composita temporis maioris ad tempus minus et velocitatis maioris ad velocitatem minorem. Exemplum: ut si mobile a moveatur per horam ut quattuor, et b per mediam horam ut duo … in quadruplo maius spatium pertransit a in hora quam b in media hora.

In modern notation the three propositions together say

$$
\frac{s_1}{s_2} = \frac{t_1}{t_2}\cdot\frac{v_1}{v_2},
$$

which is the ratio form of $s = v\,t$ for uniform motion. The proof has exactly the structure of the modern derivation. The first proposition gives $s \propto t$ at constant speed; the second gives $s \propto v$ at constant time; the third passes through an intermediate motion $(v_2, t_1)$:

$$
\frac{s(v_1,t_1)}{s(v_2,t_2)}
= \frac{s(v_1,t_1)}{s(v_2,t_1)} \cdot \frac{s(v_2,t_1)}{s(v_2,t_2)}
= \frac{v_1}{v_2}\cdot\frac{t_1}{t_2}.
$$

Alvarus's words are _si a et b moverentur aequaliter in illis duobus temporibus inaequalibus_ (the intermediate motion), and then _modo a in aliqua proportione quae sit f maiori velocitate movetur quam tunc_ (the second factor).

His example gives $\frac{1}{1/2}\cdot\frac{4}{2} = 4$. It happens to match uniform acceleration from rest: with $v = g\,t$ and $g = 4$, the speed is $4$ after one hour and $2$ after half an hour, and the distances $s = \tfrac12 g t^2$ are $2$ and $\tfrac12$, again in ratio $4$. Alvarus's example, however, concerns two uniform motions, and he does not draw that connection.

**Why no quotient?** It is tempting to explain this by the nature of time: time comes from change, so speed would only be a relation between one motion and another. That is only partly right.

| Explanation | Assessment |
|---|---|
| Time arises only from change, so it cannot be a divisor | Not the main reason. Aristotle defines time as "the number of motion with respect to before and after" (_Physics_ IV.11), so time depends on motion. But time is still a continuous quantity that can be divided and measured. Alvarus counts in hours, and Aristotle provides a standard: the uniform rotation of the heavens (_Physics_ IV.14). |
| A ratio holds only between magnitudes of the same kind | The real obstacle (Euclid, _Elements_ V, def. 3). $s_1 : s_2$ and $t_1 : t_2$ are ratios; $s : t$ is not. |
| Speed is known only by comparing one motion with another | Yes, but the comparison need not involve two bodies. The 1 : 3 rule (section 2.4) compares the two halves of a single motion. |
| Speed had no number | No. A speed is a degree (_gradus_) in a latitude and receives a number: _moveatur per horam ut quattuor_. |
| A peculiarity of the scholastics | No. Galileo still states his theorems as ratios (_in duplicata ratione_, section 3). Velocity as a quotient $ds/dt$ became standard only around 1700 (Varignon). |

Speed is thus a **degree of a quality** that can be compared with other degrees, like a degree of heat. Its relation to distance and time is stated through ratios of like to like, because the theory of proportion did not allow unlike magnitudes to be divided.

**Example: 20 km/h.** Let $a$ move at 20 for 3 hours and $b$ at 5 for 2 hours (Alvarus would use leagues, _leucae_, not kilometres).

| | Today | Alvarus |
|---|---|---|
| What the speed is | A quotient: $v = s/t$ = 20 km / 1 h | A degree _ut viginti_ in the latitude of velocity |
| Unit | km/h, formed by dividing a unit of length by a unit of time | None. The number places the degree only relative to other degrees: _ut decem_ is half of it, _ut quadraginta_ double. |
| How it is tied to distance | Built into the unit: 20 km in each hour | By its effect: the distance _natum pertransiri illo gradu … per idem tempus continuato_, which the degree would cover if held uniformly for a given time (fifth proposition, section 2.4) |
| Distances of $a$ and $b$ | $s_a = 20 \cdot 3 = 60$ km, $s_b = 5 \cdot 2 = 10$ km | $\dfrac{s_a}{s_b} = \dfrac{20}{5}\cdot\dfrac{3}{2} = 4 \cdot \dfrac32 = 6$: $a$ covers six times the distance of $b$ (_proportio sextupla_) |
| Absolute distance | Obtained directly | Obtained only if one distance is already known: if $b$ covers 10 leagues, $a$ covers 60 |

Alvarus's route to the $6$ follows the same three steps as his third proposition above, with the intermediate motion "5 for 3 hours":

$$
\frac{s(20,3)}{s(5,2)}
= \underbrace{\frac{s(20,3)}{s(5,3)}}_{\text{2nd prop.: }20/5\,=\,4}
\cdot \underbrace{\frac{s(5,3)}{s(5,2)}}_{\text{1st prop.: }3/2}
= 6.
$$

The modern unit also contains a comparison: 20 km/h means "20 times the speed that covers 1 km in 1 h". The difference is that km/h is itself a quantity that can be multiplied by a time to give a distance: $20 \text{ km/h} \times 3 \text{ h} = 60 \text{ km}$. The degree _ut viginti_ cannot be multiplied by an hour. Every calculation passes through the composition of ratios, and its result is a ratio (_sextupla_), not a distance.

**Recovering 20 km/h with a reference motion.** Absolute distances can still be obtained by choosing a **reference motion**, the degree that covers 1 km in 1 hour, and composing ratios against it. The second ratio must be time to time (1 h : 1 h), not 1 km : 1 h, because a distance and a time have no ratio. The kilometre enters only through the reference motion's distance.

| Step | Ratio | Kind |
|---|---|---|
| Speed of $a$ to the reference speed | $20 : 1$ | degree : degree |
| Time of $a$ to the reference time | $1\text{ h} : 1\text{ h} = 1 : 1$ | time : time |
| Composed (third proposition) | $\tfrac{20}{1}\cdot\tfrac{1}{1} = 20$ | distance : distance |
| Reference distance (given) | 1 km | absolute |
| Distance of $a$ | $20 \times 1\text{ km} = 20$ km in one hour | absolute |

For 3 hours only the time ratio changes: $\tfrac{20}{1}\cdot\tfrac{3}{1} = 60$, so $a$ covers 60 km. This matches the modern $20 \text{ km/h} \times 3 \text{ h}$ above.

| | Today | With a reference motion |
|---|---|---|
| The unit | One quantity, km/h | A pair kept apart: (1 km, 1 h) |
| The result of the calculation | A distance: $20\text{ km/h}\times 3\text{ h} = 60$ km | A ratio of distances, $60 : 1$, which becomes 60 km only when multiplied by the reference distance |

The reference motion plays the role of the modern unit. The medieval texts come close to this: in the 1 : 3 rule Alvarus fixes a reference distance ("in the first half it covers one league", section 2.4), and his fifth proposition identifies a degree by the distance it "would cover if continued for the same time". In this language "20 km/h" becomes "the degree that, held uniformly for one hour, covers twenty times what the reference degree covers in one hour."

**Apples and oranges.** The everyday saying that one cannot compare apples with oranges is Euclid's rule in plain words. _Elements_ V, def. 3 allows a ratio only between magnitudes "of the same kind". Def. 4 gives the test: two magnitudes have a ratio if some multiple of one can exceed the other. No number of hours ever exceeds a kilometre.

| Operation | Euclid | Modern dimensional analysis |
|---|---|---|
| Compare unlike: is 3 km greater than 2 h? | No ratio (def. 4) | Meaningless |
| Add unlike: 3 km + 2 h | Meaningless | Meaningless |
| Ratio of like: 60 km : 10 km | Yes, _sextupla_ | Yes, the pure number 6 |
| Divide unlike: 20 km / 1 h | Not defined | Written, and taken to define a new kind of quantity, speed |

The intuition survives today for comparing and adding. The only change is the last row, and even there the "division" of a length by a time can be read in two ways:

| Reading | What 20 km/h means | Relation to the medieval practice |
|---|---|---|
| Shorthand | Two ratios of like to like, $s : 1\text{ km} = 20$ and $t : 1\text{ h} = 1$, followed by the division of the pure numbers $20/1$. "km" and "h" are labels recording which reference was used. | The reference motion above, written compactly. Newton, _Arithmetica universalis_ (1707), defines number as "the abstract ratio of any quantity to another quantity of the same kind, which is taken for unity". |
| Quantity calculus | A quantity is a number times a unit, and units are multiplied and divided as algebraic symbols. km/h is a unit of a new kind. A rigorous theory came only in the twentieth century (Whitney 1968). | A formal extension that Euclid's theory does not contain, though it does not contradict it |

On the first reading, 20 km/h does not really divide a length by a time; it is shorthand for the separated form. The compact notation nevertheless earns its place, because its cancellation of units performs the composition of ratios automatically:

$$
20\,\frac{\text{km}}{\text{h}} \times 3\text{ h}
= \underbrace{\frac{20}{1}}_{\text{degree : degree}}
\cdot \underbrace{\frac{3\text{ h}}{1\text{ h}}}_{\text{time : time}}
\cdot \underbrace{1\text{ km}}_{\text{reference distance}}
= 60\text{ km}.
$$

The h cancelling against h is the time ratio of the table above, and the km left over is the reference distance. The separated form is better for explaining the calculation, and the compact form for carrying it out.

Practice was ahead of theory. Merchants' arithmetic, from Fibonacci's _Liber abaci_ (1202) onward, treated "so much money per pound" as plain numbers in the rule of three. Euclid's restriction weighed on geometry and natural philosophy, not on commerce. Nor did it stop the Calculators from reaching their results: with ratios alone they obtained the mean-speed rule, the 1 : 3 rule, and the infinite series of section 2.6. What they lacked was a single quantity, speed, that could be multiplied by a time to give a distance. That convenience arrived only when ratios to units began to be treated as numbers.

### 2.3 The mean-speed rule

For motion that is uniformly difform with respect to time, the whole motion is as fast as a uniform motion at the degree reached at the middle instant (p. 133):

> Et quando dicitur quod motus uniformiter difformis quo ad tempus velocitas debet attendi penes gradum medium qui est in medio temporis, volumus dicere quod tam velociter movetur in illo tempore adaequate illud mobile ac si per totum illud tempus moveretur illo gradu quem habet in medio illius temporis.

Alvarus presents this as the _communior opinio_. It is the Merton mean-speed rule, first formulated at Oxford by Heytesbury and proved geometrically by Oresme in the 1350s.

In modern terms, if the degree of speed grows uniformly, $v(t) = v_0 + a\,t$ on $[0,T]$, then

$$
s = \int_0^T (v_0 + a\,t)\,dt = v_0 T + \tfrac12 a T^2
= \frac{v_0 + v_T}{2}\,T
= v\!\left(\tfrac{T}{2}\right) T .
$$

The average of the extreme degrees equals the degree at the middle instant, and the distance is that of a uniform motion at this degree. Oresme's proof is the same computation done with areas: the "quantity" of a uniformly difform motion is represented by a trapezium (or a triangle when $v_0 = 0$) whose base is the time and whose heights are the degrees. This trapezium has the same area as the rectangle whose height is the middle degree. Alvarus's parallel rule for motion uniformly difform **with respect to the subject** (a rotating wheel, whose points move faster the farther they are from the centre) replaces time by the length of the moving body, $\bar v = v(\text{midpoint of the radius})$.

### 2.4 The 1 : 3 rule and the half-distance rule

In the chapter _De motu locali quo ad effectum secundum tempus difformi_ (p. 148):

> _Quarta propositio._ Omnis potentia movens uniformiter difformiter latitudine terminata ad non gradum in triplo plus pertransit in medietate in qua movetur intensius quam in medietate temporis in qua movetur remissius … Ex quo sequitur quod si a mobile moveatur per horam uniformiter difformiter incipiendo a non gradu usque ad certum gradum, et in prima medietate unam leucam pertransit, in secunda medietate trium leucarum spatium absolvet. Et si ordine praepostero moveri incepisset, puta ab illo dato gradu usque ad non gradum, in prima medietate horae tribus absolutis leucis, una dumtaxat restaret transeunda in secunda temporis medietate.

> _Quinta propositio._ Si aliquod mobile moveatur uniformiter difformiter a non gradu usque ad certum gradum in aliquo tempore, ipsum adaequate subduplum spatium pertransit ad spatium natum pertransiri illo gradu intensiori per idem tempus continuato.

The reasoning for the fourth proposition is explicitly the ratio law of section 2.2: _temporibus existentibus aequalibus … spatia pertransita se habent in ea proportione in qua se habent velocitates_. With velocity rising uniformly from $0$ to $V$ in time $T$:

$$
s\left(0,\tfrac{T}{2}\right) = \frac{VT}{8}, \qquad
s\left(\tfrac{T}{2},T\right) = \frac{3VT}{8}, \qquad
s(0,T) = \frac{VT}{2}.
$$

The same 1 : 3 statement reappears in the fourth treatise (p. 285). Alvarus gives only the halves; the full series of odd numbers $1, 3, 5, 7, \ldots$ for successive equal times, and the general law $s \propto t^2$, are not stated in the passages found.

Both follow at once from the same premises. With $v(t) = \dfrac{V}{T}\,t$,

$$
s(t) = \frac{V}{2T}\,t^2 ,
\qquad
s\big((k-1)\tau,\,k\tau\big) = \frac{V\tau^2}{2T}\,(2k-1),
$$

so the distances in successive equal intervals $\tau$ are as $1:3:5:7:\cdots$, and their running sums $1, 4, 9, 16, \ldots$ are the squares. Alvarus's case is $\tau = T/2$, $k = 1, 2$. The **decelerating** case (_ordine praepostero_) is the same motion run backwards, $3 : 1$. The **fifth proposition** is the case $v_0 = 0$ of the mean-speed rule: $s = \tfrac12 V T$, half of the distance $V T$ that the final degree would cover in the same time.

### 2.5 Linear and angular speed

Alvarus distinguishes the speed of circular motion, measured by the line a point traces, from the speed of **revolution**, measured by the angle described about the centre (p. 138):

> Velocitas enim motus circularis attenditur penes lineam descriptam a certo puncto … Sed velocitas circuitionis attendi habet penes angulum descriptum in tanto vel tanto tempore circa centrum: ita quod si in aequali tempore duo mobilia, sive aequalia sive inaequalia, circulariter mota aequales angulos circa centrum describunt, ipsa aequaliter circueunt.

This is the distinction between linear and angular velocity. For a point at distance $r$ from the centre,

$$
v = \omega\, r, \qquad \omega = \frac{\Delta\theta}{\Delta t},
$$

so two wheels of different size that describe equal angles in equal times _aequaliter circueunt_ (equal $\omega$), although their rims move with different linear speeds. Within one wheel the linear speed is uniformly difform **with respect to the subject**, rising linearly from $0$ at the centre to $\omega R$ at the rim, which is why the mean-speed rule of section 2.3 applies to it.

### 2.6 Infinite series

The treatise sums infinite series routinely, which has drawn the attention of historians of mathematics. For example (p. 276), a body is composed of infinitely many parts whose contributions to its total whiteness decrease continually in quadruple ratio, the first being "as two":

> … igitur ibi sunt infinitae denominationes continuo se habentes in proportione quadrupla descendendo, et prima est ut duo: igitur aggregatum ex omnibus simul est ut duo cum duabus tertiis.

That is, $2 + \tfrac12 + \tfrac18 + \cdots = \dfrac{2}{1 - \tfrac14} = \dfrac{8}{3}$, an instance of

$$
\sum_{n=0}^{\infty} a\,q^{n} = \frac{a}{1-q}\qquad (0 < q < 1).
$$

The decrease "in quadruple ratio" is the product of two halvings. Each successive part is half as long (_in subdupla parte_), and its whiteness is half as intense (_subduplae intensionis_), so its contribution is $\tfrac12 \cdot \tfrac12 = \tfrac14$ of the preceding one. This is the composition of ratios of section 2.2 applied to intensity and extension instead of speed and time.

The same technique underlies the Calculators' problems in which a mobile moves "as $2$ in the first proportional part of an hour, as $4$ in the second" and so on (Dolz, _Cunabula_ 33; see section 12 of the [analysis](Cunabula-analysis.html)). If the hour is divided in double proportion, the $n$-th part lasts $2^{-n}$ hours, and the distance is

$$
s = \sum_{n=1}^{\infty} v_n\,2^{-n}.
$$

The distance is finite when the speeds grow arithmetically, $v_n = n + 1$ (Dolz's $2, 3, 4, \ldots$; the sum is $3$), and infinite when they grow geometrically, $v_n = 2^n$ (every term is $1$). Deciding which such series converge is exactly what these cases required.

The example also shows how thoroughly the two genres of section 1 are fused: a problem about the intension of a quality is solved by summing a geometric series of proportions.

### 2.7 What Alvarus says about falling bodies

The only discussion of the acceleration of a falling body found in the treatise (p. 90) repeats Aristotle and explains the acceleration by the **medium**, not by any law of motion:

> Motus naturalis factus per medium uniforme velocior est in fine quam in principio, ut inquit Philosophus octavo _Physicorum_ textu commenti septuagesimi sexti; cuius causa talis a naturalibus assignatur: quod illud medium minus resistit in fine quam in principio, quia tunc minor pars eius restat dividenda.

He adds an appeal to experience: swimmers who dive to the bottom of a river and come back up find that the water resists them less the nearer they are to the surface. The uniformly difform motion of sections 2.3–2.4 is **not** applied to free fall.

Within the framework of section 1.1 this explanation is coherent. If the weight $F$ stays constant while the effective resistance $R(s)$ of the medium still to be divided decreases with the distance fallen, then $F/R(s)$ increases and so does $v = k\log\big(F/R(s)\big)$. The acceleration is thus a matter of dynamics _penes causam_, and nothing in the argument makes it uniform in time.

---

## 3. Alvarus beside Galileo

Galileo's _Discorsi e dimostrazioni matematiche intorno a due nuove scienze_ (Leiden, 1638), Third Day, _De motu naturaliter accelerato_:

| Result | Alvarus (1509) | Galileo (1638) |
|---|---|---|
| Definition | _motus uniformiter difformis quo ad tempus_: equal increments of degree in equal times | "Motum aequabiliter, seu uniformiter, acceleratum dico illum, qui, a quiete recedens, temporibus aequalibus aequalia celeritatis momenta sibi superaddit." |
| Mean speed | p. 133: as fast as the degree at the middle of the time | Theorem I: the time is equal to that of a uniform motion "cuius velocitatis gradus subduplus sit ad summum et ultimum gradum velocitatis prioris motus uniformiter accelerati" |
| Half the distance at final speed | p. 148, fifth proposition: _subduplum spatium … ad spatium natum pertransiri illo gradu intensiori per idem tempus continuato_ | Equivalent to Theorem I |
| Halves of the time | p. 148: 1 league, then 3 leagues | Corollary I to Theorem II: $1, 3, 5, 7, \ldots$ in successive equal times |
| Distance and time squared | Not stated | Theorem II: "spatia … sunt inter se in duplicata ratione eorundem temporum" |
| Applied to falling bodies | No: acceleration explained by the medium (p. 90) | Yes: the central claim of the Third Day |
| Experimental test | None | The inclined plane |

In modern notation, Galileo's Third Day amounts to

$$
v = g\,t, \qquad s = \tfrac12 g\,t^2, \qquad v^2 = 2 g\, s,
$$

of which the medieval theorems supply the passage from the first formula to the second, **given** the first. The first formula is what Galileo asserted of falling bodies.

Galileo opens the Third Day by claiming novelty: it has been observed that the natural motion of heavy bodies accelerates, "verum iuxta quam proportionem eius fiat acceleratio, proditum hucusque non est: nullus enim, quod sciam, demonstravit, spatia a mobili descendente ex quiete peracta in temporibus aequalibus, eam inter se retinere rationem, quam habent numeri impares ab unitate consequentes." The claim is accurate for **falling bodies**. It is not accurate for uniformly difform motion in the abstract, for which Oresme had already given the series of odd numbers and Alvarus the 1 : 3 case.

---

## 4. What Galileo added

### 4.1 From imagination to nature

The Calculators and Alvarus treated uniformly difform motion _secundum imaginationem_: as one logically possible case among many, applicable to any quality that admits degrees. The theorems are demonstrated as conditionals — **if** a motion is uniformly difform in time, **then** the distances are as 1 : 3 — without asserting that any real motion satisfies the antecedent. Galileo's decisive step was to assert the antecedent of falling bodies. Before him, Domingo de Soto (_Quaestiones super octo libros Physicorum_, revised edition 1551) had already stated, briefly and by way of example, that falling bodies and projectiles move with uniformly difform motion; William Wallace has argued that this is the first such statement in print.

### 4.2 Choosing the right hypothesis

A mathematical proof establishes the conditional; it does not choose which law nature follows. Several hypotheses were consistent with "natural motion is faster at the end":

- **Aristotle**: speed set by weight against the resistance of the medium.
- **Alvarus** (p. 90): acceleration because less of the medium remains to be divided.
- **Pardo** (_Principiorum Phisicorum_, 13a): "quanto magis descendit ad suum locum, tanto velocius movetur" — speed increasing with **distance fallen**.
- **Galileo in 1604**: in his letter to Paolo Sarpi of 16 October 1604 (_Opere_ X, 115–116) he derived the times-squared law from the premise that speed is proportional to the distance fallen.

Galileo later rejected the distance hypothesis in the _Discorsi_ by argument rather than measurement. His argument is disputed as stated, but the conclusion is correct. The two hypotheses lead to quite different motions:

$$
\frac{dv}{dt} = g \;\Longrightarrow\; s(t) = \tfrac12 g t^2,
\qquad\qquad
\frac{ds}{dt} = k\,s \;\Longrightarrow\; s(t) = s_0\, e^{k t}.
$$

With $s_0 = 0$ the second has only the solution $s \equiv 0$, so a body obeying it could never start from rest. And if it were displaced by any small $s_0 > 0$, it would move exponentially, which no one observes. Reasoning therefore eliminated one candidate; it could not by itself establish that nature chooses uniform increase in **time**.

The correct relation between speed and distance is $v = \sqrt{2 g s}$. Speed does grow with the distance fallen, as Pardo and Aristotle say (_quanto magis descendit … tanto velocius_), but in proportion to its square root, not to the distance itself. The qualitative medieval statement is true; it was the step to a simple proportion that misled Galileo in 1604.

### 4.3 Experiment

In the _Discorsi_ the mathematical derivation comes first; the inclined-plane experiment is introduced when Simplicio asks for evidence. Alexandre Koyré (_Études galiléennes_, 1939) argued that Galileo's experiments were largely thought experiments. Stillman Drake ("Galileo's Discovery of the Law of Free Fall", _Scientific American_, 1973) showed from Galileo's working papers (MS Gal. 72, f. 116v, c. 1604) that he did make and record measurements. Galileo thus combined a demonstrated conditional, the claim that nature satisfies its antecedent, and an experimental check — the combination that none of his predecessors had assembled.

### 4.4 Beyond kinematics

Much of what Galileo is known for has no counterpart in Alvarus:

- bodies of different weight fall at the same rate (with forerunners in Philoponus and Benedetti, not in the Calculators);
- a persistence of motion close to inertia, replacing both Aristotle's mover and the impetus of Buridan, Coronel, and Celaya;
- the composition of independent motions and the parabolic trajectory of projectiles;
- the telescopic discoveries, the defence of Copernicus, and the programme of a nature "written in mathematical language".

### 4.5 In short

For the **kinematic theorems**, most of what textbooks attribute to Galileo is medieval, and Alvarus had the mean-speed rule, the half-distance rule, and the 1 : 3 case in print by 1509. For the **physics** — the claim that falling bodies actually obey these theorems, its experimental support, and the new theory of motion built on it — the credit is Galileo's.

---

## 5. Duhem and the historiography

**Pierre Duhem**, _Études sur Léonard de Vinci_ (3 vols., Paris, 1906–1913), rediscovered this material. The third volume carries the subtitle _Les précurseurs parisiens de Galilée_ (1913). It discusses the Parisian physics of the early sixteenth century, including Alvarus Thomas, Dullaert, Luis Coronel, and Celaya, and presents Domingo de Soto as the author who applied uniformly difform motion to falling bodies. Duhem's thesis was that the science of Galileo was not a victory of modern science over medieval philosophy, but the long-prepared triumph of the physics born at Paris in the fourteenth century — Buridan's impetus and Oresme's kinematics — over Aristotle and Averroes. The pages on [Celaya](../Juan-de-Celaya/) and [Luis Coronel](../Luis-Coronel/) record Duhem's specific judgements on those authors.

**Correctives.** Duhem overstated continuity, to the point of making Galileo a follower of the Parisians.

- **Anneliese Maier** (_Die Vorläufer Galileis im 14. Jahrhundert_, 1949) and **Marshall Clagett** (_The Science of Mechanics in the Middle Ages_, 1959) documented the medieval theorems precisely while showing that their conceptual framework — latitudes of forms, _secundum imaginationem_ — differed from Galileo's.
- **Alexandre Koyré** (_Études galiléennes_, 1939) located Galileo's novelty in the mathematization of nature itself, not in particular theorems.
- **William A. Wallace** traced a concrete path of transmission: "The Enigma of Domingo de Soto: _Uniformiter difformis_ and Falling Bodies in Late Medieval Physics" (_Isis_ 59, 1968); "The _Calculatores_ in Early Sixteenth-Century Physics" (_British Journal for the History of Science_ 4, 1969); _Galileo's Early Notebooks: The Physical Questions_ (1977); _Galileo and His Sources_ (1984); _Domingo de Soto and the Early Galileo_ (2004). Galileo's early Latin notebooks (MS Gal. 46) draw on lecture notes of Jesuit professors at the Collegio Romano, who in turn drew on Soto and the Parisian tradition.

**Does Galileo cite Alvarus?** Not as far as is known. Galileo does not name Alvarus or Soto; any link is indirect. The borrowing of the early notebooks from the Jesuit lectures is widely accepted; whether that route carried the specific kinematics from Soto to Galileo remains debated.

The present consensus is roughly the one in section 4.5: the theorems are medieval, the physics is Galileo's, and the sixteenth-century Parisian and Spanish authors form the bridge between them that the standard account usually omits.

---

## 6. Transmission: from Oxford to Salamanca

### 6.1 Origins (fourteenth century)

- **Oxford**: Bradwardine (1328), Heytesbury (1335), Swineshead ("the Calculator", c. 1350), Dumbleton — the intension of forms, latitudes of motion, the mean-speed rule, and the law relating speed to the ratio of power to resistance.
- **Paris**: Buridan (impetus), Oresme (geometrical configurations of qualities, a geometrical proof of the mean-speed rule, the odd-number series), Albert of Saxony.

### 6.2 Italy (fifteenth century)

After about 1400 the calculatory tradition faded at Paris, where realism and then humanism dominated; the royal edict of 1474 even banned nominalist teaching until its revocation in 1481. It remained alive in **Italy**, at Padua and Pavia, where Swineshead and Heytesbury were commented on and, from the late fifteenth century, printed. The "Bassanus" named by Dolz alongside Bradwardine and Oresme points to the Italian proportion literature available in print around 1500. The Parisian revival was thus, in part, an import through Italian printed editions.

### 6.3 The Paris revival (c. 1495–1530)

| Person | Role | On this site |
|---|---|---|
| **John Mair** (regent at Montaigu from 1496) | Organizer of the nominalist revival rather than a mathematician; teacher of the Coronels and Lax | [John Mair](../John-Mair/) |
| **Jerónimo Pardo** (d. 1502/1505) | Mair's friend; announced a treatise _de intensione_ that was never written (section 7) | [Jerónimo Pardo](../Jeronimo-Pardo/) |
| **Jean Dullaert of Ghent** (_Physics_ questions, 1506) | Physics of impetus; source for Coronel; cited by Dolz on _Physics_ III | — |
| **Alvarus Thomas** (_Liber de triplici motu_, 1509) | The mathematical core: proportions, motion by cause and effect, mean speed, 1 : 3, series (section 2) | Life: section 8 |
| **Luis Coronel** (_Physicae perscrutationes_, 1511) | Physics shaped by Dullaert and Alvarus; impetus; cites Swineshead | [Luis Coronel](../Luis-Coronel/) |
| **Gaspar Lax** (_Arithmetica_ and _Proportiones_, 1515; _Calculationes_, 1517; _Quaestiones physicales_, Zaragoza, 1527) | Systematic mathematics of proportions and calculations; teacher of Celaya, Dolz, Vitoria, Vives | [Gaspar Lax](../Gaspar-Lax/) |
| **Juan de Celaya** (_Physics_, 1517) | Seventy-one folios on motion surveying the Mertonians, Paris, and Padua; calls Lax _regentis mei_; teacher of Soto and Vitoria | [Juan de Celaya](../Juan-de-Celaya/) |
| **Juan Dolz** (_Cunabula_, 1518) | Elementary textbook; names Bradwardine, Oresme, Bassano, Alvarus, Lax; compares Alvarus, Lax, and Dullaert on terminology | [Juan Dolz](index.html) |
| **Domingo de Soto** (_Physics_ questions, 1545; revised 1551) | Applies uniformly difform motion to falling bodies | [Domingo de Soto](../Domingo-de-Soto/) |

Schematically:

1. Oxford Calculators and Oresme (fourteenth century)
2. Italian commentaries and printed editions (fifteenth century)
3. Mair's circle at Montaigu; Pardo's announcement (c. 1500)
4. Alvarus (1509) → Luis Coronel (1511), Lax (1515–1517)
5. Celaya (1517), Dolz (1518); Lax's _Quaestiones physicales_ at Zaragoza (1527)
6. Soto (1545, 1551) → Jesuits of the Collegio Romano → Galileo's early notebooks

### 6.4 Advance or transmission?

Mostly systematization and teaching, with some genuine advances:

- **Alvarus** is the most original: a vast classification of difform motions and routine summation of infinite series.
- **Lax** gives the most rigorous mathematical treatment of proportions.
- **Dolz** makes the explicit pedagogical move of turning specialist mathematics into an elementary curriculum "not to make mathematicians but philosophers" (see the introduction to the [analysis](Cunabula-analysis.html)).
- **Soto** takes the step that matters for Galileo: uniformly difform motion is the motion of real falling bodies.

### 6.5 A second eclipse, and the Spanish return

The tradition nearly disappeared from Paris a second time. Humanists attacked the whole calculatory style; Juan Luis Vives, himself a student of Lax, published _In pseudodialecticos_ in 1519–1520. By the 1530s the calculatory physics had largely faded at Paris. It survived because the Spaniards took it home: Lax to Zaragoza, Celaya to Valencia, Soto to Salamanca, and through Salamanca and Alcalá into the Jesuit curriculum. The rescue came less from any single Parisian than from this Spanish return.

Lax is the clearest case. Self-taught in mathematics (_nullo doctore_, as he wrote to his student E. de Melo), he left Paris around 1521 and continued to publish calculatory material at Zaragoza. His _Quaestiones physicales_ (Zaragoza, 1527) treat quantity, the whole, _de maximo et minimo_, the infinite, motion _penes causam_, and rarity and density. The question on motion opens with the "famous difficulty" of what the speed of any motion follows as its cause (_penes quid tanquam penes causam cuiuscumque motus velocitas attendatur_) and rejects four positions before giving his own. Near its end it compares speeds in equal and unequal times by what the mobile acquires or loses (_quod acquiret vel deperdet_). The book has no section on motion _penes effectum_, so the mean-speed rule and the question of falling bodies should not be expected there.

---

## 7. Jerónimo Pardo: an early programmatic witness

Pardo died before any of the Parisian calculatory works appeared, but he shows that the programme was on the agenda at Montaigu around 1500:

- In the prologue to the [_Medulla Dyalectices_](../Jeronimo-Pardo/Medulla-Dyalectices-1505.html) he announces that he will later add "difficilem philosophiam quae de intensione dicitur".
- The physics text attributed to him, [_Principiorum Phisicorum_](../Jeronimo-Pardo/Principiorum-Phisicorum-et-Introductiones-Librorum-Animae.html), refers three times (12b, 15a, 29a) to a _Tractatus de intensione formarum_. No such treatise is known in any library, in print or in manuscript; it was apparently never written.
- He already reads the relevant authorities: Buridan and Heytesbury in the _Medulla_, Albert of Saxony in the physics text.
- His surviving account of local motion (13a) is Aristotelian, without degrees, latitudes, or proportions — but it ties the acceleration of a falling stone to the distance fallen, the hypothesis Galileo held in 1604 (section 4.2).

Pardo is therefore not the founder of the revival. The tradition was older, and Mair was at Montaigu at the same time. He is, however, the earliest Spanish witness on this site to the intention of taking up the Calculators' _de intensione_ at Paris, almost a decade before Alvarus.

---

## 8. Alvarus Thomas: what is known of his life

Alvarus has no page of his own on this site, since he was Portuguese, not Spanish. What is known of him is collected here. The documented facts cover only about twelve years, 1509–1521. The main modern summary is Leitão (2000), who draws the archival data from Matos (1950) and Villoslada (1938). The rest comes from the 1509 edition itself: its title, its explicit, and the letters and poems printed with it.

| Name form | Where |
|---|---|
| _Alvarus Thomas_, genitive _Alvari Thome_ | Title page and dedication of 1509 |
| _Ulixbonensis_ | "of Lisbon", title page and explicit |
| Álvaro Tomás | Modern Portuguese |
| Alvaro Thomaz | Wallace, _Dictionary of Scientific Biography_; English Wikipedia |
| _Albarus_, _Neotericus Albarus_ | Spanish authors (Margalho) |

### 8.1 Timeline

| Date | Event | Source |
|---|---|---|
| c. 1480–1485 | Born in Lisbon | Birthplace: title page. Date: Leitão's estimate from the rest of the career |
| c. 1500 | Arrives in Paris as a young arts student, at about 16–18 | Leitão's conjecture, by comparison with other Portuguese students at Paris |
| before 1509 | Master of arts; regent at the Collège de Coqueret, where he has finished one complete course of teaching | Bruniau's letter (section 8.3): he wrote the book in six months _secundum in Coqueretico stadio curriculum expectans_, "while waiting for his second course at Coqueret" |
| 7, 9, and 11 February 1509 (probably 1510 in modern reckoning) | Prefatory letters dated from Coqueret (7 and 9 February); explicit dated 11 February | 1509 edition |
| 1513 | Still regent in arts at Coqueret; enrolls in the Faculty of Medicine | Leitão, after Matos and Villoslada |
| c. 1515 | Licentiate examinations in medicine | Leitão |
| 1518 | Doctor of medicine; appointed to teach in the Faculty of Medicine | Leitão |
| 1521 | Last signature in the university records | Leitão |
| after 1521 | Unknown. Place and date of death unknown | — |

The explicit reads:

> Explicit liber de triplici motu compositus per Magistrum Alvarum Thomam Ulixbonensem Regentem Parrhisius in Collegio Coquereti. Anno domini 1509. Die Februarii 11.

**The date.** At Paris the year began at Easter, so 11 February 1509 in the explicit is 11 February 1510 by modern reckoning. Leitão keeps 1509, following most authors, and refers to Soares (2000, p. 225) for the problem. This page keeps 1509 as the conventional date of the book.

**Regent of arts, then medicine.** A regent was usually a master of arts who paid for his studies in a higher faculty (theology, law, or medicine) by teaching the arts course in a college. A regent took one group of students through the whole course, which lasted about three and a half years. Bruniau's "second course" therefore means that Alvarus had already taken one group through the whole course at Coqueret before 1509. He wrote the _Liber de triplici motu_ in the gap before the next group began. His move to medicine in 1513 follows the usual pattern, and it also fits his age: a man who became doctor of medicine in 1518 was probably not much older than thirty-five at the time.

**The Collège de Coqueret.** Founded in 1439, Coqueret never had the standing of Montaigu or Sainte-Barbe. In these years it had Alvarus and Juan de Celaya as teachers. Later, in the 1540s, it was the college of Jean Dorat, Ronsard, and Du Bellay.

### 8.2 Was he a student of Mair?

| Question | Answer | Evidence |
|---|---|---|
| Did he study under Mair? | No evidence that he did | Leitão: "There is no evidence of Thomas being directly associated with Major or of having been his direct disciple, but no doubt he benefited from the intellectual environment around the Scottish master." |
| Same college? | No | Alvarus taught at Coqueret; Mair taught at Montaigu |
| Who was his teacher? | A "Petrus de Alliaco" | Bruniau's letter: _praeceptorem tuum Petrum de Alliaco_ (see below) |
| Does the _Liber de triplici motu_ cite Mair? | Not found by name | Wallace (DSB) counts Mair among the authors Alvarus knew. A search of the ECHO transcription for Mair's name found no citation; abbreviated forms may have been missed |
| Which way did influence run? | Partly from Alvarus to Mair's circle | Luis Coronel, Mair's student, excerpted Alvarus in his _Physicae perscrutationes_ (1511) |
| Was he part of the same milieu? | Yes | The same university, the same years, the same nominalist logic and physics; Mair's students held chairs in the other colleges |

So the answer is no, as far as the documents show. Alvarus belongs to the same Parisian generation and the same nominalist milieu as Mair's students, but not to the circle of Mair's direct pupils. He came to the Calculators from a different direction. Mair's interest in the infinite and in the intension of forms came through logic and theology; Alvarus's came through mathematics.

**"Petrus de Alliaco".** Bruniau writes that Alvarus has a better claim to the name of philosopher than anyone in that crowd of philosophers:

> … ut praeceptorem tuum Petrum de Alliaco inter philosophiae professores dum viveret doctissimum aut aequaveris aut (quod potius crediderim) superaveris, quem si fata virum servassent huic Parisiorum academiae omnibus philosophiae studiosis fructus non parum (quod sperabant omnes) procul dubio attulisset.

"… so that you have either equalled or (as I would rather believe) surpassed your teacher Pierre d'Ailly, the most learned of the professors of philosophy while he lived. Had the fates spared him, he would no doubt have brought great profit to all students of philosophy at this University of Paris, as everyone hoped."

| Reading | For | Against |
|---|---|---|
| The cardinal Pierre d'Ailly (1351–1420), whose logic and physics were read and printed at Paris | Leitão takes it this way: "One of his contemporaries considered him to be superior to Pierre d'Ailly" | _praeceptorem tuum_ ("your teacher") and _dum viveret_ ("while he lived"); "had the fates spared him … as everyone hoped" fits a master who died young, not a cardinal who died at about seventy, ninety years earlier |
| A recent Paris master of the same name, Alvarus's own teacher, who died before fulfilling his promise | The wording fits it better | No such master has been identified here |

The question is left open in section 9.

### 8.3 The people around the 1509 edition

| Person | Role in the book | What the book says about him |
|---|---|---|
| **Pedro de Meneses** | Dedicatee: _asylo protectorique suo_, "his refuge and protector" | A Portuguese nobleman, learned in letters, whom Alvarus had known personally. He travelled to Paris to hear its masters. His brothers had won military fame in North Africa |
| **Georgius Bruniau** of Vendôme | Letter to Alvarus, dated from Coqueret, 7 February | Praises Alvarus's learning in theology, both laws, moral and natural philosophy, the quadrivium, and Cicero and Livy. Says the book was written in six months |
| **Hermann Lethmate** of Gouda | Addressee of two pieces by Ioannes de Haya | Procurator of the German nation, though "barely out of boyhood". He was Alvarus's pupil (_Alvaro Thomae … addictus es_) and saw the book into print |
| **Ioannes de Haya** | Verses and a letter to Lethmate, dated from Coqueret, 9 February | Calls Alvarus "a second Gorgias of Leontini", who has an argument ready for anything |
| **Dionysius Faber** of Vendôme | Eight-line poem to the reader | Read the book twice, and it will please more |
| **Guillaume Anabat** | Printer, praised in verses at the end | — |

Leitão calls the author of the letter "Gregoire Bruneau"; the ECHO transcription reads _Georgius Bruniau vindocinensis_. Hermann Lethmate of Gouda is probably Hermannus Lethmatius (c. 1492–1555), later a doctor of theology, dean of St Mary's at Utrecht, and a correspondent of Erasmus. A birth around 1492 fits "barely out of boyhood" in 1509–1510; the identification should be checked.

The book had three Coqueret letters, a pupil from the German nation who paid attention to its printing, and a Portuguese patron. It was a college product, written by a regent in the time between two courses and seen through the press by his circle.

### 8.4 Colleagues and readers

| Person | Relation to Alvarus | Source |
|---|---|---|
| **Juan de Celaya** | Colleague at Coqueret. His _Physics_ (1517) draws on the _Liber de triplici motu_ without naming it | Leitão; Wallace 1969 |
| **Robert Caubraith** | Scottish colleague at Coqueret | Wikipedia, after Wallace; not checked |
| **Luis Coronel** | Excerpts Alvarus in the _Physicae perscrutationes_ (1511) | Wallace 1969 |
| **Juan Dolz** | Names him (_si Aluarum_), cites his _Proportiones_ II.1 and II.3, and compares his terminology with that of Lax and Dullaert | [Analysis](Cunabula-analysis.html) |
| **Pedro Margalho** (Portuguese) | Cites the "Neotericus Albarus" | Leitão; Wallace |
| **Pedro de Espinosa**, **Diego de Astudillo** | Praise and cite him; Astudillo often, in his questions on _De generatione_ | Leitão; Wallace |
| **Domingo de Soto** | Uses the substance of his treatises, seldom naming sources; possibly through Celaya, Soto's teacher at Paris | Wallace; Leitão |
| **Alonso de la Veracruz** | Critic: applied to Alvarus's calculations the words of Luke 5:5, "we have laboured all the night and taken nothing" | Wallace |

Two judgements give his standing among contemporaries. Wallace: "At Paris […] there can be little doubt that Thomaz was the calculator par excellence at the beginning of the sixteenth century, and the principal stimulus for the revival of interest there in the Mertonian approach to mathematical physics." Villoslada (p. 190, quoted after Leitão), comparing him with Celaya: "El maestro lusitano era, por su ecletismo, su erudición y dialética invencible, gemelo de Celaya e superior a él como matemático."

### 8.5 Modern rediscovery

| Year | Author | Contribution |
|---|---|---|
| 1741 | Barbosa Machado, _Bibliotheca Lusitana_ I, 114–115 | Bibliographical entry |
| 1913 | Duhem, _Études sur Léonard de Vinci_ III, 532–543 | First modern analysis of the book |
| 1914 | Wieleitner | His summation of infinite series |
| 1926 | Rey Pastor, _Los matemáticos españoles del siglo XVI_ | A chapter on the book; calls him "digno precursor de Pedro Nunes" and asks Portuguese scholars to search the archives for his biography |
| 1950 | Matos, _Les Portugais à l'Université de Paris_ | Archival data on his career |
| 1959 | Clagett | Places him in the medieval mechanical tradition: "he has at his command the whole medieval mechanical tradition" |
| 1969, 1976 | Wallace | BJHS article; DSB entry "Thomaz, Alvaro" |
| 1989 | Sylla | The disputational context of his mathematics |
| 2000 | Leitão | Collects the biographical evidence |

The _Liber de triplici motu_ is, as far as is known, his only work: 141 folios in two columns of small gothic type. Wieleitner called it a _liber rarissimus_, but Leitão counted more than twenty surviving copies, which suggests a wide circulation for a book of 1509.

Rey Pastor's 1926 request has still not been met. Leitão's warning also stands: references to Alvarus's life in the secondary literature often contain errors, so each claim should be traced to Matos, Villoslada, or the 1509 edition.

---

## 9. Open questions and points to verify

- **Italian printing history** of Swineshead and Heytesbury before 1510, and the identity of Dolz's "Bassanus" (probably Bassano Politi), should be checked against a bibliography before citation.
- **Soto's passage**: quote it from the 1551 edition rather than from secondary summaries; Wallace (1968) gives the text and context.
- **Duhem's treatment of Alvarus**: Leitão gives _Études_ III, pp. 532–543; check the chapter and read it (the site already cites pp. 135–141 and 242–246 for Celaya).
- **"Petrus de Alliaco"** in Bruniau's letter (section 8.2): the cardinal, or a recent Paris master who taught Alvarus? Élie (1950–51) and Villoslada may name such a master.
- **Alvarus's archival record**: read Matos (1950) and Villoslada (1938) directly for the 1513 enrolment in medicine, the 1518 doctorate, and the last signature in 1521.
- **Pedro de Meneses** and **Hermann Lethmate**: identify the dedicatee, and confirm that Lethmate is the later Utrecht theologian.
- **Lax's _Calculationes_ (1517)** and **Coronel's _Physicae perscrutationes_ (1511)**: whether either contains the mean-speed rule, the 1 : 3 rule, or an application to falling bodies.
- **Lax's _Quaestiones physicales_ (Zaragoza, 1527)**, not yet transcribed. Its sections are _de quantitate_, _de toto_, _de maximo et minimo_, _de infinito_, _de motu penes causam_ and _de raritate et densitate_; there is no section on motion _penes effectum_. The question _de motu penes causam_ opens by reviewing four erroneous positions on what speed follows. Near its end it compares speeds in equal and unequal times by what is acquired or lost, apparently the same composition of ratios as Alvarus p. 149. Printed at Zaragoza after Lax's return, it belongs to the Spanish phase of section 6.5. It appeared before Soto's _Physics_ questions (1545, 1551), so it is not chronologically excluded as a source for Soto.
- **Mair**: whether his _Physics_ or _Sentences_ commentaries contain calculatory kinematics, or only the discussions of the infinite.
- **Alvarus**: whether the treatise anywhere extends the 1 : 3 result to thirds, quarters, or the odd-number series.

---

## References

### Primary sources

- Alvarus Thomas. _Liber de triplici motu proportionibus annexis magistri Alvari Thome Ulixbonensis philosophicas Suiseth calculationes ex parte declarans_. Paris, 1509. ECHO XML transcription.
- Dolz del Castellar, Juan. _Cunabula omnium fere scientiarum_. Montauban, 1518. [Transcription](Cunabula-omnium-fere-scientiarum-1518.html).
- Euclid. _Elements_. Book V, definitions 3–4.
- Fibonacci (Leonardo of Pisa). _Liber abaci_. 1202.
- Galilei, Galileo. Letter to Paolo Sarpi, 16 October 1604. _Le Opere di Galileo Galilei_, Edizione Nazionale, X, 115–116.
- Galilei, Galileo. _Discorsi e dimostrazioni matematiche intorno a due nuove scienze_. Leiden, 1638. Third Day.
- Newton, Isaac. _Arithmetica universalis_. Cambridge, 1707.
- Pardo, Jerónimo. _Medulla Dyalectices_. Paris, 1505. [Transcription](../Jeronimo-Pardo/Medulla-Dyalectices-1505.html).
- Pardo, Jerónimo (attr.). _Principiorum Phisicorum et Introductiones Librorum Animae_. Institución Colombina, MS 7-2-29. [Transcription](../Jeronimo-Pardo/Principiorum-Phisicorum-et-Introductiones-Librorum-Animae.html).
- Soto, Domingo de. _Super octo libros Physicorum Aristotelis quaestiones_. Salamanca, 1545; revised edition, 1551.

### Secondary literature

- Clagett, Marshall. _The Science of Mechanics in the Middle Ages_. Madison, 1959.
- Crosby, H. Lamar. _Thomas of Bradwardine: His Tractatus de Proportionibus_. Madison, 1955.
- Drake, Stillman. "Galileo's Discovery of the Law of Free Fall." _Scientific American_ 228 (1973).
- Duhem, Pierre. _Études sur Léonard de Vinci_. 3 vols. Paris, 1906–1913. Vol. III: _Les précurseurs parisiens de Galilée_ (1913).
- Élie, Hubert. "Quelques maîtres de l'Université de Paris vers l'an 1500." _Archives d'histoire doctrinale et littéraire du Moyen Âge_ 18 (1950–51), 193–243.
- Koyré, Alexandre. _Études galiléennes_. Paris, 1939.
- Leitão, Henrique. "Notes on the life and work of Álvaro Tomás." _Boletim do Centro Internacional de Matemática_ 9 (2000), 10–15. [Archived copy](https://web.archive.org/web/20050527074241/http://at.yorku.ca/i/a/a/h/11.htm).
- Maier, Anneliese. _Die Vorläufer Galileis im 14. Jahrhundert_. Rome, 1949.
- Matos, Luís de. _Les Portugais à l'Université de Paris entre 1500 et 1550_. Coimbra, 1950.
- Rey Pastor, Julio. _Los matemáticos españoles del siglo XVI_. Toledo, 1926.
- Soares, Luís Ribeiro. _Pedro Margalho_. Lisbon, 2000.
- Sylla, Edith D. "Alvarus Thomas and the Role of Logic and Calculations in Sixteenth Century Natural Philosophy." In S. Caroti (ed.), _Studies in Medieval Natural Philosophy_. Florence, 1989, 257–298.
- Villoslada, Ricardo G. _La Universidad de París durante los estudios de Francisco de Vitoria, O.P. (1507–1522)_. Rome, 1938.
- Wallace, William A. "The Enigma of Domingo de Soto: _Uniformiter difformis_ and Falling Bodies in Late Medieval Physics." _Isis_ 59 (1968), 384–401.
- Wallace, William A. "The _Calculatores_ in Early Sixteenth-Century Physics." _British Journal for the History of Science_ 4 (1969), 221–232.
- Wallace, William A. _Galileo's Early Notebooks: The Physical Questions_. Notre Dame, 1977.
- Wallace, William A. _Galileo and His Sources: The Heritage of the Collegio Romano in Galileo's Science_. Princeton, 1984.
- Wallace, William A. _Domingo de Soto and the Early Galileo_. Aldershot, 2004.
- Wallace, William A. "Thomaz, Alvaro." In C. C. Gillispie (ed.), _Dictionary of Scientific Biography_, vol. 13, p. 350. New York, 1976.
- Wieleitner, Heinrich. "Zur Geschichte der unendlichen Reihen im christlichen Mittelalter." _Bibliotheca Mathematica_, 3. Folge, 14 (1914), 150–168.
- Whitney, Hassler. "The Mathematics of Physical Quantities." _American Mathematical Monthly_ 75 (1968), 115–138 and 227–256.
