# Transcription Rules

### 1. Column and Page Flow
* **One Column at a Time**: Process the entire first column from top to bottom, append its specific footnotes, and only then move to the second column.
* **No Text Duplication**: Text crossing over or splitting at the bottom of a column is never repeated when the next column or page begins.
* **No Added Labels**: Page markers like "(p. 1)" or "(Page 2)" are completely omitted from the text output, as they are not part of the original printed file.

### 2. Typographical Fidelity
* **Line-by-Line Breaks**: Every line break in the printed text is mirrored exactly in the transcription to preserve the original spacing and line lengths.
* **Original Orthography**: Keep the historical spelling exactly as printed, including the use of **u** and **v** (e.g., `vici`, `ut`), **i** and **j** (e.g., `iuuat`, `JOANNIS`), and original abbreviations if present.
* **Hyphenation**: Words split across two lines by a hyphen are kept split with a hyphen (e.g., `obli- / gatio`) to match the print layout.

### 3. Structural Elements
* **Paragraph Indentations**: Column paragraphs are visually preserved by using six empty spaces (`      `) to match the indentation style of the typeset blocks.
* **Footnote Isolation**: Footnotes/critical notes are detached from the running text and placed strictly at the absolute bottom of the specific column they belong to.
* **Editorial Brackets**: 
    * Angle brackets `< >` are used for modern section headings or text insertions supplied by the editor.
    * Square brackets `[ ]` indicate folio markers (e.g., `[fo.vii.rb]`) or editorial emendations inside the footnotes (e.g., `¹⁸ probatione<m>`).

### 4. Added Formatting Constraints
* **Markdown Block**: Wrap everything inside a standard markdown code block.
* **Page Anchors**: Prepend the number of the page to the very beginning of the block in the style `[page X]`, and add a blank line.
* **Uppercase Formatting Spacer**: Add a blank line immediately before any line that is completely written in uppercase.
* **Clean Layout Labels**: Do not include any structural indicators like `### Column X`.
* **Separate all columns with `---` and two empty lines, one above and the other below the separator** like:  
  (empty line)
  ---
  (empty line)

