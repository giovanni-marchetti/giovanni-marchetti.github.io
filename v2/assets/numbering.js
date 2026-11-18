// Numbering of the Primer, as in LaTeX. The definitions, theorems and examples (<div class="definition">, "theorem"
// and "example", lemmas, corollaries and propositions included) are numbered in the order of the page, with one
// counter. The label of a block holds only its kind, and a link to a block is left empty: it gets the block's name,
// like \ref, or only its number if the link has class="num".
//
//   <div class="theorem" id="thm-constructible"><p><span class="label">Theorem</span> Statement.</p></div>
//   ... by <a href="#thm-constructible"></a> ...                                     shows  ... by Theorem 3 ...
//   ... Theorems <a class="num" href="#thm-a"></a> and <a class="num" href="#thm-b"></a> ...   shows  ... Theorems 20 and 24 ...
//
// A label gets a period, as in "Theorem 3.", unless a name in parentheses follows it, as in "Lemma 17 (Lelong).".
// A block inside an HTML comment is not on the page, so it takes no number. An empty link to an id that is not a
// numbered block shows "??", as in LaTeX, and the console names the id. Links with text keep it. No libraries.

(() => {
  "use strict";

  const blocks = new Map();   // id of a numbered block -> its kind and number, such as "Theorem" and 3
  let count = 0;

  document.querySelectorAll(".definition, .theorem, .example").forEach(block => {
    const label = block.querySelector(".label");
    if (!label) return;
    count++;
    const kind = label.textContent.replace(/[\s\d.]+$/, "");   // a number written by hand is replaced
    const next = label.nextSibling;
    const named = next !== null && next.nodeType === Node.TEXT_NODE && next.data.trimStart().startsWith("(");
    label.textContent = kind + " " + count + (named ? "" : ".");
    if (block.id) blocks.set(block.id, { kind, number: count });
  });

  document.querySelectorAll('a[href^="#"]').forEach(link => {
    if (link.children.length || link.textContent.trim()) return;
    const id = link.getAttribute("href").slice(1);
    const block = blocks.get(id);
    if (!block) {
      link.textContent = "??";
      console.warn(`numbering.js: no numbered block with id "${id}"`);
    } else {
      link.textContent = link.classList.contains("num") ? String(block.number) : block.kind + " " + block.number;
    }
  });
})();
