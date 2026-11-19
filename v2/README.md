# Neuroalgebraic Geometry website

A plain HTML website. There is no build step: open `index.html` in a browser.

## Files

| File | Contents |
|:--|:--|
| `index.html` | Home page |
| `primer.html`, `literature.html`, `open-problems.html`, `community.html` | The other pages |
| `assets/style.css` | Colors, type and layout |
| `assets/mathjax-config.js` | LaTeX settings and shared macros |
| `papers.js` | The papers listed on the Literature page, and the tags that filter them |
| `assets/literature.js` | Writes the papers of `papers.js` into `literature.html`, and above them the tags |
| `assets/numbering.js` | Numbers the definitions, theorems and examples of the Primer, and fills in the empty links to them |
| `assets/sections.js` | Opens a collapsed section of the Primer when a link points inside it |
| `assets/toggles.js` | Buttons that change a figure: the skip connections and the weight sharing of the network in the Examples of the Primer |
| `neuromanifold/` | The two interactive neuromanifold viewers: `surface.js` (the surface of a residual network, `#nm-surface`, at the end of the home page), `flat.js` (the flat neuromanifold of a shallow network, `#nm-flat`, at the end of the section "Feature learning" of the Primer), and `viewers.css`, the styles of both |

## Writing math

Math is rendered by MathJax, so you can write LaTeX directly in the HTML:

- Inline `$...$`, display `$$...$$`.
- Numbered equations: `\begin{equation}\label{eq:name} ... \end{equation}`, referenced with `\eqref{eq:name}`.
- Shared macros (`\R`, `\C`, `\K`, `\M`, `\Sym`, `\din`, `\dout`, `\dpar`, `\rank`) are defined in `assets/mathjax-config.js`. Add your own there.
- A literal dollar sign is written `\$`.

Theorem-like blocks are plain HTML; see `primer.html`. Their numbers are automatic (`assets/numbering.js`): the label
holds only the kind, and the id (`def-`, `thm-`, `lem-`, `cor-`, `prop-` or `ex-`, then a name) is used to refer to
the block. Definitions and theorems (lemmas, corollaries and propositions included) are drawn in a shaded box, in the
light orange of the highlighted buttons (`--orange-tint`, at the top of `assets/style.css`).

```html
<div class="theorem" id="thm-name"><p><span class="label">Theorem</span> Statement.</p></div>        <!-- Theorem 3. -->
<div class="definition" id="def-name"><p><span class="label">Definition</span> (Name). Text.</p></div>  <!-- Definition 4 (Name). -->
<div class="example" id="ex-name"><p><span class="label">Example</span> (Name). Text.</p></div>        <!-- Example 5 (Name). -->
<details class="proof"><summary>Proof.</summary><p>Text.</p></details>  <!-- collapsible, starts closed -->
<div class="bend"><p>A subtle point, marked by a "dangerous bend" sign in the margin.</p></div>
```

Definitions, theorems (lemmas, corollaries and propositions included) and examples share one counter, in the order of
the page; a block inside an HTML comment takes no number. A label gets a period unless a name in parentheses follows
it. To refer to a block, leave the link empty: it shows the block's name, like `\ref`, or only its number if the link
has `class="num"`. An empty link to an id that is not a numbered block shows "??".

```html
... by <a href="#thm-name"></a> ...                                                      <!-- by Theorem 3 -->
... Theorems <a class="num" href="#thm-a"></a> and <a class="num" href="#thm-b"></a> ...  <!-- Theorems 20 and 24 -->
```

Other pages cannot know these numbers: a link from them to a block of the Primer names it in words, without a number.

Each section of the Primer is collapsible and starts closed (add `open` to start it open):

```html
<details class="section">
  <summary><h2 id="name">Title</h2></summary>
  ...
</details>
```

A section can be divided into subsections, each starting with `<h3 id="name">Title</h3>`.

## Citing in the Primer

The Primer ends with a References section, sorted by the surname of the first author. To cite a work, add its entry
there (ids follow the convention of `papers.js`) and link to it in the text, author–year, with "et al." for three or
more authors:

```html
<li id="pinkus1999approximation">Allan Pinkus. <cite>Approximation Theory of the MLP Model in Neural Networks.</cite> Acta Numerica 8, 143–195, 1999. <a href="https://doi.org/10.1017/S0962492900002919">doi:10.1017/S0962492900002919</a></li>

... (<a href="#pinkus1999approximation">Pinkus, 1999</a>) ... <a href="#pinkus1999approximation">Pinkus (1999)</a> proves ...
```

## Adding a paper

The papers on the Literature page are listed in `papers.js`, one entry per paper:

```js
{
  id: "kileel2019expressive",
  authors: "Joe Kileel, Matthew Trager, Joan Bruna",
  title: "On the Expressive Power of Deep Polynomial Neural Networks",
  venue: "Advances in Neural Information Processing Systems (NeurIPS)",
  year: 2019,
  link: "https://arxiv.org/abs/1905.12207",
  topics: "Universal approximation, Dimension and degree, Identifiability",
  architecture: "MLP",
  activation: "Monomial",
},
```

To add a paper, copy an entry, paste it anywhere in the list and change its fields; the comment at the top of `papers.js` describes them. The page sorts the papers by first author, so their order in the file does not matter. LaTeX works as in the pages, except that each backslash is written twice: `"$\\mathbb{R}^n$"`. Other pages link to a paper by its `id`, for example `literature.html#kileel2019expressive`.

### Tags

The tags of a paper (`topics`, `architecture`, `activation`) are listed in `TAGS`, at the top of `papers.js`, with what each one covers. The topics follow the sections of the Primer: one per section, except that "Dimension, degree, sample complexity" has two, *Dimension and degree* and *Sample complexity*, and "Learning" is *Distance minimization*. A tag's `primer` field names the part of the Primer about it; the page does not show it at present.

Above the list, the Literature page shows the tags as buttons, each with the number of papers it would show. A reader can select several: a paper is shown if, in every row with a selected tag, it has one of the selected tags (so *MLP* and *CNN* show the papers on either, and *Identifiability* and *CNN* the papers on the identifiability of CNNs). The selection is kept in the address of the page, so a link can open the list already filtered, for example `literature.html?topics=identifiability&architecture=cnn`; the address writes each tag in lowercase, with hyphens between words (`dimension-and-degree`).

## Adding a page

1. Copy an existing page, for example `community.html`, and change its title and content.
2. Add a link to the new page in the menu (`<nav class="site-nav">`) of every page.
3. In the new page's menu, put `aria-current="page"` on its own link.

## Publishing

Any static host works. On GitHub, push this folder to a repository and enable Pages under Settings → Pages.
