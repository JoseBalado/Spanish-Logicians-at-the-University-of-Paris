# markdown-preview.css

This file is a **VS Code Markdown Preview** stylesheet. It has no effect on the Jekyll site or GitHub Pages — it is purely a local editing aid.

## What it does

When you open a `.md` file in VS Code and use the built-in preview (`Ctrl+Shift+V` or the side-by-side preview), VS Code can load custom CSS to style the rendered output. `markdown-preview.css` defines the `.textus` class so that `<div class="textus">` blocks in the Latin transcriptions render with the same large-print serif look you see on the deployed website:

```css
.textus {
    font-size: 1.7em;
    line-height: 1.6;
    font-family: Georgia, serif;
}
```

Without this file the preview would ignore the `textus` class and show those blocks in the default body font.

## How to enable it

Add this to your VS Code **settings.json** (workspace or user level):

```json
{
  "markdown.styles": ["markdown-preview.css"]
}
```

The path is relative to the workspace root.

## Why it exists

The Latin transcription files wrap primary-source quotations in `<div class="textus">…</div>`. On the deployed site the `medieval` layout defines its own `.textus` styles (with background colour, border, etc.). This small CSS file mirrors the essential typographic properties so you can proof-read transcriptions inside VS Code without running Jekyll.
