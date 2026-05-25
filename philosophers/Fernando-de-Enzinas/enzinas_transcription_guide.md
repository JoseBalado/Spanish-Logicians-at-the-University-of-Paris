# Transcription Guide: Enzinas 1528 — Learned Corrections


## Folio Markers

Insert page markers **inline within the sentence**, exactly where the column break occurs in the original — not at the start of a new paragraph.

The text flows continuously. When a new column begins (/9.1b/, /9.2a/ etc.):
- Insert the folio marker inline
- Continue the sentence without a paragraph break
- Do NOT treat the column break as a new paragraph

---

**Correct:**
```markdown
...atque hominem /9.1a/ esse animal; ergo intellectus...
```

**Incorrect:**
```markdown
/9.1a/
nem esse animal: ergo intellectus...
```

The text flows continuously across folios; the marker is a reference point, not a break.

---

## Accusativus cum Infinitivo (AcI) — Hyphens

Always connect AcI constructions with hyphens. This is one of the most important
logical-structural rules.

**Correct:**
- `hominem-esse-animal`
- `Sortem-currere`

**Incorrect:**
- `hominem esse animal`
- `hominem esse-animal`

Apply consistently every time an AcI construction appears, even mid-sentence.

---

## Punctuation: Colons vs Commas

The original uses colons heavily, but modern transcription should use commas where
Latin syntax calls for it — especially in relative clauses and enumerations.

Colons usually appear before ergo, explanatory phrases, or continuing the paragraph with second opinions.

**Correct:**
```markdown
nec valet ad hoc dicere voluntatem, quando vult, hominem-esse-animal habere volitionem
terminatam ad homines tantum, et etiam aliam terminatam ad animalia
```

**Incorrect:**
```markdown
nec valet ad hoc dicere voluntatem: quam qualis homines esse animal habere volitione:
quia voluntas terminará ad animalia
```

---

## Abbreviation Expansions — Specific Cases

These specific expansions were confirmed or corrected:

| Original form | Correct expansion |
|---|---|
| `vnica` | `unica` |
| `qp` | `quod` |
| `7` | `et` |
| `9` suffix | `us` (e.g., `corp9` → `corpus`) |
| `ergo` | `ergo` (do not alter) |
| `atq3` | `atque` |
| `neq3` | `neque` |
| `q3` suffix | `que` (e.g., `eliq3` → `eisque`, `eiiq3` → `eisque`) |
| `postq¨3` | `postquam` |
| `vtrique` | `utrique` |
| `vnam` | `unam` |
| `prouenit` | `provenit` |
| `novae` | restore diphthong (not `nove`) |
| `quaecumque` | restore diphthong (not `quecumque`) |
| `nulli` | restore (not `nulli` misread) |
| `synonyme` | restore diphthong → `synonymae` |
| `primae consequentiae` | restore diphthong (not `prime consequentie`) |

---

## U vs V Rule — Stricter Application

**V is NEVER used when followed by a vowel** — always normalize to U in those positions.

- `vult` → `vult` (V followed by consonant: keep V? No — normalize to U always for vowel function)
- `unica` not `vnica`
- `unam` not `vnam`
- `unum` not `vnum`

**Exception:** V is kept only when functioning as a consonant (e.g., `voluntas`, `valet`).

**Rule of thumb:** If the letter sounds like a vowel U, write U. If it sounds like consonant V, write V.

---

## Quotes Around Propositions

Use double quotes for complete propositions being analyzed:

```markdown
post formationem huius propositionis "Homo est animal" compositae
```

```markdown
### Quartodecimo: Cur potius huius mentalis "Homo est animal" notitia hominum sit subiectum quam notitia animalium.
```

Use single quotes for isolated terms and syncategorematic particles (*ly*) referenced as linguistic objects:

```markdown
nec cum illa copula 'est'
```

```markdown
Utrum ly 'futurus' et alii consimiles termini syncategoremata sint.
```

---

## Pilcrow (¶) Size Hierarchy

The text uses two distinct sizes of ¶ that signal different structural levels:

- **Large ¶** — marks a major section opener, a new argumentative block. Render as `##` heading. The full title of the section follows on the same line, including subordinate clauses.
  - Example: `## Circa igitur opinionem hanc ponentem syncategorema in anima nihil significare.`
- **Small ¶** — marks individual subordinate items within a section, such as numbered *difficultates*. Each small ¶ renders as a `###` heading containing the full question, followed by any continuation prose as a plain paragraph.
  - Example: `### Difficultas prima ergo erit: Utrum actu syncategorematici dicantur immutare intellectum.`

**Important:** The `###` heading contains the full statement of the *difficultas* as a question. Continuation prose (e.g., further elaboration or the answer) follows as a plain paragraph beneath it, not as part of the heading.

**Correct:**
```markdown
### Quartodecimo: Cur potius huius mentalis "Homo est animal" notitia hominum sit subiectum quam notitia animalium.

Seu quod idem est: Cur potius in hac mentali "Omnis albedo est qualitas" (cum ly 'omnis'
tam immediatum sit subiecto sicut praedicato) distribuatur subiectum quam praedicatum.
```

**Incorrect:**
```markdown
### Quartodecimo cur potius huius mentalis...
Seu quod idem est...
```

---

## Word Corrections — Common Misreadings

These words were misread and corrected:

| Misread | Correct |
|---|---|
| `volitatis` | `volitatis` — check carefully against context |
| `fallumanic` | `falsum` (misread) |
| `nouam` | normalize to `novam` |
| `opositum` | `oppositum` |
| `prospositionaliter` | `propositionaliter` |
| `Holect` | `Holkot` (proper name: Robert Holcot) |
| `optratui` | `optativi` |
| `solui` | `solvi` (normalize to classical spelling) |
| `quinis` | `quivis` (misread — "whoever" not "five each") |
| `isto in primo die` | `sto in prius dictis` (significant misread) |
| `dissensione` | `dissensu` (wrong case) |
| `impendientes` / `impendentes` | `impedientes` (from *impedio*, "mutually cancelling") |
| `eliq3` / `eiiq3` / `eisq3` | `eisque` (ablative + *que* suffix) |
| `notiam categorematicam concurrere et fectine` | `notiam categorematicam concurrere effectine` |

---

## Proper Names

- **Hieronymus Hangest** — always two words, capital H on both
- **Hieronymus Pardo** — always two words, capital H and P (scholastic author cited in the *difficultates*)
- **Holkot** — not "Holect" or "Holket" (refers to Robert Holcot, scholastic theologian)
- **Gregorii** — genitive of Gregorius (refers to Gregory of Rimini)

---

## HTML Comments for Editorial Notes

Use HTML comments for uncertainty, alternative readings, or editorial notes.
These are invisible on the rendered GitHub Pages site.

```markdown
<!-- unclear: possibly 'conservatur' — check another copy -->
<!-- Google AI read this as X -->
<!-- abbreviation expansion uncertain here -->
```

---

## General Accuracy Reminders

- **Read slowly** — many errors come from reading too fast and pattern-matching to common words
- **Check word endings** — Latin inflections are critical for meaning; `-am`, `-um`, `-em` are not interchangeable; `ab` always governs the ablative (never accusative)
- **No inventions** — if a word is illegible, use `<!-- illegible -->` rather than guessing
- **Diphthongs** — always restore `ae` where the original has `e` in classical Latin words (`synonymae`, `primae`, `consequentiae`, etc.)
- **Paragraph count** — verify the same number of paragraphs appear in transcription as in the source column
- **`q3` suffix reads as letters** — in degraded print, `eisque` can appear as `eliq3`, `eiiq3`, or `eisq3`; always check the image and the grammar before expanding
- **`ab` governs ablative** — if an expansion after `ab` yields an accusative form, the reading is wrong; re-examine the image
