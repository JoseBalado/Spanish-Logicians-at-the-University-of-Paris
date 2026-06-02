

# HTML Tags for Font Size in Markdown — Comparison Table
## All inside one tag

| Feature                                 | `<div>`                                                                  | 
|-----------------------------------------|--------------------------------------------------------------------------|
| Markdown inside works                   | No                                                                          | 
| New line (return). Avoid using it.      | First line needs "new line" or <br />. Following lines need <br />       |
| One line (return plus new line)         | First line needs <br /><br />. Following lines <br /><br /> or one line. Use always  <br /><br /> |
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |
| **Verdict**                             | **best long-term**                                     | 





| Feature                                 | `<p>`                                                                  | 
|-----------------------------------------|--------------------------------------------------------------------------|
| Markdown inside works                   | No                                                                          | 
| New line (return). Avoid using it.      |       |
| One line (return plus new line)         |          |
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |





| Feature                                 | `<span>`                                                                  | 
|-----------------------------------------|--------------------------------------------------------------------------|
| Markdown inside works                   | No                                                                          | 
| New line (return). Avoid using it.      |       |
| One line (return plus new line)         |          |
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |





| Feature                                 | `<big>`                                                                  | 
|-----------------------------------------|--------------------------------------------------------------------------|
| Markdown inside works                   | No                                                                          | 
| New line (return). Avoid using it.      |       |
| One line (return plus new line)         |          |
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |








# HTML Tags for Font Size in Browser — Comparison Table
## All inside one tag

| Feature                                 | `<div>`                                                          | 
|-----------------------------------------|-----------------------------------------------------------------------------|
| Markdown inside works                   | No                                                                | 
| Single line (return). Avoid using it.   | Needs <br />.                                                               |
| One line (return plus new line)         | Needs <br /><br />                                                          | 
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |
| **Verdict**                             | **best long-term**                                     | 





| Feature                                 | `<p>`                                                                  | 
|-----------------------------------------|--------------------------------------------------------------------------|
| Markdown inside works                   | No                                                                          | 
| New line (return). Avoid using it.      |       |
| One line (return plus new line)         |          |
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |





| Feature                                 | `<span>`                                                                  | 
|-----------------------------------------|--------------------------------------------------------------------------|
| Markdown inside works                   | No. And layont gets completelly mangled.                                                                          | 
| New line (return). Avoid using it.      |       |
| One line (return plus new line)         |          |
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |





| Feature                                 | `<big>`                                                                  | 
|-----------------------------------------|--------------------------------------------------------------------------|
| Markdown inside works                   | No. And layont gets completelly mangled.                                                                          | 
| New line (return). Avoid using it.      |       |
| One line (return plus new line)         |          |
| Font size control                       |                                                        | 
| One tag per paragraph needed            |                                                        | 
| Clutter in raw text                     |                                                        | 
| Deprecated in HTML5                     |                                                        |




## Example

#### De Descensu et Ascensu
<div class="textus">
Descensus est consequentia formalis in qua a termino superiori, cum constantia, ad inferiora eius, discurritur. Ut "Omnis homo currit" et isti homines sunt omnes homines; ergo iste homo currit, et sic de singulis.
<br /><br />
In ascensu vero a singularibus cum constantia ad eorum superiora proceditur.
<br /><br />
Insuper quadruplex est descensus, scilicet, copulativus et copulatus, disiunctivus et disiunctus.
<br /><br />
Sub termino stante distributive descenditur primo modo.
<br /><br />
Sub termino stante confuse tantum copulatim, secundo modo.
<br /><br />
Sub termino stante determinate, tertio modo.
<br /><br />
Et sub termino confuse tantum disiunctim, quarto modo.
</div>

## Notes

- Tested in VSCode preview and GitHub Pages
- `<div style="font-size:1.3em">` is the recommended approach for font size control
- `<big>` is simpler but deprecated; single newlines work naturally inside it
- Neither `<p>` nor `<span>` process Markdown inside them — `*italic*` renders as literal asterisks
- CSS can target `big` globally via `markdown-preview.css` in VSCode and Jekyll CSS in GitHub Pages
