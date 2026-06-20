# Transcription — using a frontier AI to transcribe medieval logic books

A generic, reusable workflow for transcribing sixteenth-century logic books
(printed *and* manuscript) with a frontier vision model — Gemini in the web
interface, or any equivalent (Claude, etc.). No local model, no GPU: the heavy
lifting is the model's, and the quality beats specialised local HTR for this
material because the model actually *knows* scholastic Latin.

## Files

- **[PROMPT.md](PROMPT.md)** — the paste-ready prompt. Copy the whole block into
  the chat, attach the page image(s), send. It is author-agnostic.
- **README.md** — this file: the workflow, the few-shot priming method, and tips.

## Basic use

1. Open a fresh chat in Gemini (web).
2. Copy the prompt block from [PROMPT.md](PROMPT.md) and paste it.
3. Attach one or more page images.
4. Send. You get back Markdown.
5. Proofread: the model is excellent but will occasionally normalise or
   hallucinate. You always review punctuation, headings, and inflections yourself.

## Few-shot priming — provide 3 example pages per new book

This is the single biggest accuracy boost, and it is worth doing **once per new
book or manuscript**. Instead of trusting prose rules alone, you *show* the model
finished work it should imitate.

**Why 3 pages?** One example is rarely enough to capture a book's range; 3 clean,
*representative* examples teach the model your conventions far better than ten
paragraphs of instructions, without flooding the context window. Pick:

1. a **plain running-text** page (typical body text + abbreviations),
2. a page with **headings / pilcrows** (so it learns your `##` / `###` splitting),
3. a page that is **hard** — heavy abbreviation, marginalia, or (for manuscripts)
   an awkward stretch of the hand.

**How to prime, in the web interface:**

1. Paste the prompt from [PROMPT.md](PROMPT.md).
2. For each of your 3 examples: attach the **page image**, then immediately paste
   its **verified, corrected transcription** (your already-finished pages are
   ideal).
3. Add one line: *"The pages above are gold-standard examples of my conventions.
   Transcribe the NEXT image in exactly the same style."*
4. Attach the new page(s) to transcribe.

After that, within the same chat you can keep attaching new pages and the model
holds the conventions.

## Tips

- **Match the source.** Use examples from the *same* book/hand as the target.
  Print examples teach print conventions; manuscript examples teach the hand. Do
  not prime a manuscript with printed examples or vice versa.
- **Quality over quantity.** 3 *correct* examples beat 6 sloppy ones — a wrong
  example teaches wrong habits.
- **Re-prime on drift.** Long sessions fill the context window and the model
  starts to wander. When that happens, start a fresh chat and paste the prompt +
  examples again.
- **Keep a gold folder per author.** Save your best page+transcription pairs
  (e.g. `examples/Mair/`, `examples/Pardo/`) so re-priming is copy-paste.
- **Verify paragraph count** against the source column; missing paragraphs are
  the most common silent failure.
- **Build a per-book conventions note** as you go. Author-specific abbreviation
  habits and recurring misreads belong in a short per-book file kept next to that
  author's pages (e.g. `Fernando-de-Enzinas/conventions.md`), not in this generic
  prompt.
