# HTML Tags for Font Size in Markdown — Comparison Table

| Feature | `<div>` | `<p>` | `<span>` | `<big>` |
|---|---|---|---|---|
| Markdown inside works | yes | no | no | yes |
| Blank line = paragraph break | yes | no, needs `<br /><br />` | no, needs `<br /><br />` | yes |
| Single newline = line break | no, needs `<br />` | no, needs `<br />` | no, needs `<br />` | yes |
| Font size control | yes | yes | yes | no (but CSS-targetable) |
| One tag per paragraph needed | no | no | no | no |
| Clutter in raw text | medium | high | high | low |
| Deprecated in HTML5 | no | no | no | yes |
| **Verdict** | **best long-term** | avoid | avoid | good but deprecated |

## Notes

- Tested in VSCode preview and GitHub Pages
- `<div style="font-size:1.3em">` is the recommended approach for font size control
- `<big>` is simpler but deprecated; single newlines work naturally inside it
- Neither `<p>` nor `<span>` process Markdown inside them — `*italic*` renders as literal asterisks
- CSS can target `big` globally via `markdown-preview.css` in VSCode and Jekyll CSS in GitHub Pages
