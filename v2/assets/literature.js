// Literature page: writes the papers listed in papers.js into the empty list <ol id="papers">, and above the list
// the tags of TAGS (also in papers.js), which filter it. No libraries.
//
// The papers are sorted by the surname of the first author, then by year and title. Each one becomes
//   <li id="ID">Authors. <cite>Title.</cite> Venue, Year. <a href="LINK">arXiv:2501.18915</a>
//     <div class="ref-tags">Topics · Architectures · Activations activation</div>
//   </li>
// The page loads this script right after the list, before MathJax runs, so LaTeX in the papers is typeset
// with the rest of the page, and links to an entry (literature.html#ID) scroll to it.
//
// Above the list, <div class="filters"> has a column of tags for each row of TAGS, side by side. Each tag is a button that selects or unselects it, with the number of papers it would show; so is each tag under
// a paper, which stays where it is on the screen while the list changes. A paper is shown if, in every row with a
// selected tag, it has one of the selected tags: more tags in one row show more papers, tags in more rows show
// fewer. The selection is kept in the address of the page, as in literature.html?topics=identifiability&
// architecture=cnn,attention, which can be linked to. Filtering only hides entries; opening the page at an entry
// that the selection hides (literature.html?...#ID) first clears the selection.

(() => {
  "use strict";

  const list = document.getElementById("papers");
  if (!list) return;
  if (typeof PAPERS === "undefined") {
    // papers.js is missing or has a syntax error; the browser console says where.
    const message = document.createElement("p");
    message.className = "stub";
    message.textContent = "The list of papers could not be read from papers.js.";
    list.replaceWith(message);
    return;
  }

  const surname = paper => String(paper.authors || "").split(",")[0].trim().split(/\s+/).pop();
  const sentence = text => /[.?!]$/.test(text) ? text : text + ".";

  // A new element, with a class and a text if they are given.
  const make = (name, className, text) => {
    const element = document.createElement(name);
    if (className) element.className = className;
    if (text !== undefined) element.textContent = text;
    return element;
  };

  // Text of a link: "arXiv:2501.18915" for arXiv, "doi:10.4171/rmi/160" for a DOI (as in the Primer), the name of
  // the website otherwise.
  const linkText = url => {
    const arxiv = url.match(/arxiv\.org\/(?:abs|pdf)\/([^?#]+?)(?:v\d+)?(?:\.pdf)?$/);
    if (arxiv) return "arXiv:" + arxiv[1];
    const doi = url.match(/doi\.org\/(10\.[^?#]+)$/);
    if (doi) return "doi:" + decodeURIComponent(doi[1]);
    try { return new URL(url).hostname.replace(/^www\./, ""); } catch { return url; }
  };

  // A tag is known by its key: its name in lowercase, with hyphens between words ("dimension-and-degree"), as the
  // address of the page writes it. So a paper can write a tag in any case.
  const keyOf = name => String(name).toLowerCase().replace(/[^\p{L}\p{N}]+/gu, "-").replace(/^-+|-+$/g, "");
  const valuesOf = text => String(text ?? "").split(",").map(value => value.trim()).filter(Boolean);

  // The rows of TAGS, each with the keys of its selected tags, and each tag with its buttons.
  const rows = (typeof TAGS === "undefined" ? [] : TAGS).map(row => ({
    field: row.field,
    name: row.name,
    suffix: row.suffix,
    tags: (row.tags || []).map(tag => ({ ...tag, key: keyOf(tag.name), buttons: [] })),
    selected: new Set(),
  }));

  // The tags of a paper in each row, in the order of TAGS. A value missing from TAGS gets a tag at the end of its row.
  const tagsOf = paper => rows.map(row => {
    const tags = new Set();
    for (const value of valuesOf(paper[row.field])) {
      let tag = row.tags.find(known => known.key === keyOf(value));
      if (!tag) {
        console.warn(`papers.js: ${paper.id} has ${row.field} "${value}", which is not in TAGS.`);
        tag = { name: value, key: keyOf(value), buttons: [] };
        row.tags.push(tag);
      }
      tags.add(tag);
    }
    return [...tags].sort((a, b) => row.tags.indexOf(a) - row.tags.indexOf(b));
  });

  // A button that selects the tag, or unselects it, and stays where it is on the screen while the list changes.
  const tagButton = (row, tag, className) => {
    const button = make("button", className, tag.name);
    button.type = "button";
    if (tag.about) button.title = tag.about;
    button.addEventListener("click", () => {
      const top = button.getBoundingClientRect().top;
      if (row.selected.has(tag.key)) row.selected.delete(tag.key);
      else row.selected.add(tag.key);
      update();
      if (button.getClientRects().length) window.scrollBy(0, button.getBoundingClientRect().top - top);
    });
    tag.buttons.push(button);
    return button;
  };

  const papers = [...PAPERS].sort((a, b) =>
    surname(a).localeCompare(surname(b), "en") ||
    (a.year || 0) - (b.year || 0) ||
    String(a.title || "").localeCompare(String(b.title || ""), "en"));

  // The entries of the list, each with the tags of its paper in each row.
  const entries = papers.map(paper => {
    const item = document.createElement("li");
    if (paper.id) item.id = paper.id;
    if (paper.authors) item.append(sentence(paper.authors) + " ");
    if (paper.title) {
      const cite = document.createElement("cite");
      cite.textContent = sentence(paper.title);
      item.append(cite);
    }
    const where = [paper.venue, paper.year].filter(Boolean).join(", ");
    if (where) item.append(" " + sentence(where));
    if (paper.link) {
      const a = document.createElement("a");
      a.href = paper.link;
      a.textContent = linkText(paper.link);
      item.append(" ", a);
    }
    // The tags, row after row. They are left out of the order of the Tab key, since the same tags are above the list.
    const tags = tagsOf(paper);
    const line = make("div", "ref-tags");
    rows.forEach((row, r) => {
      if (!tags[r].length) return;
      if (line.firstChild) line.append(" · ");
      tags[r].forEach((tag, i) => {
        const button = tagButton(row, tag, "ref-tag");
        button.tabIndex = -1;
        if (i) line.append(", ");
        line.append(button);
      });
      if (row.suffix) line.append(" " + row.suffix);
    });
    if (line.firstChild) item.append(line);
    list.append(item);
    return { item, tags };
  });

  // Above the list: a column of tags for each row of TAGS, each tag with the number of papers it would show.
  const bar = make("div", "filters");
  for (const row of rows) {
    const group = make("div", "filter-row");
    const name = make("span", "filter-name", row.name);
    name.id = "filter-" + keyOf(row.field);
    group.setAttribute("role", "group");
    group.setAttribute("aria-labelledby", name.id);
    const tags = make("div", "filter-tags");
    for (const tag of row.tags) {
      tag.pill = tagButton(row, tag, "tag");
      tag.count = make("span", "tag-count");
      tag.pill.append(" ", tag.count);
      tags.append(tag.pill);
    }
    group.append(name, tags);
    bar.append(group);
  }
  if (rows.length) list.before(bar);

  const none = make("p", "stub", "No paper matches the selected tags.");
  list.after(none);

  // Whether an entry has, in every row with a selected tag, one of the selected tags. The row `except` is skipped.
  const matches = (entry, except) => rows.every((row, r) =>
    row === except || !row.selected.size || entry.tags[r].some(tag => row.selected.has(tag.key)));

  // Shows the entries that match the selection, and updates the buttons, the numbers and the address of the page.
  function update() {
    let count = 0;
    for (const entry of entries) {
      entry.item.hidden = !matches(entry);
      if (!entry.item.hidden) count += 1;
    }
    rows.forEach((row, r) => {
      for (const tag of row.tags) {
        const pressed = String(row.selected.has(tag.key));
        for (const button of tag.buttons) button.setAttribute("aria-pressed", pressed);
        // The papers that this tag would show with the selection of the other rows.
        const n = entries.filter(entry => entry.tags[r].includes(tag) && matches(entry, row)).length;
        tag.count.textContent = n;
        tag.pill.classList.toggle("tag-none", n === 0);
      }
    });
    none.hidden = count > 0 || !rows.some(row => row.selected.size);
    writeAddress();
  }

  function clearSelection() {
    for (const row of rows) row.selected.clear();
    update();
  }

  // The selection, in the address of the page: ?topics=identifiability,singularities&architecture=cnn.
  function writeAddress() {
    const params = new URLSearchParams(location.search);
    for (const row of rows) {
      const keys = row.tags.filter(tag => row.selected.has(tag.key)).map(tag => tag.key);
      if (keys.length) params.set(row.field, keys.join(","));
      else params.delete(row.field);
    }
    const query = params.toString().replace(/%2C/gi, ",");
    const search = query ? "?" + query : "";
    if (search === location.search) return;
    try {
      history.replaceState(history.state, "", (search || location.pathname) + location.hash);
    } catch {
      // Not allowed by some browsers for a page opened from a file; the address then keeps the old selection.
    }
  }

  const address = new URLSearchParams(location.search);
  for (const row of rows) {
    for (const value of valuesOf(address.get(row.field))) {
      const tag = row.tags.find(known => known.key === keyOf(value));
      if (tag) row.selected.add(tag.key);
    }
  }
  update();

  // An address pointing to an entry that the selection hides first clears the selection, so that the browser can
  // scroll to it.
  const reveal = id => {
    let target = null;
    try { target = id && document.getElementById(decodeURIComponent(id)); } catch { return null; }
    if (!target || !target.hidden || target.parentElement !== list) return null;
    clearSelection();
    return target;
  };
  window.addEventListener("hashchange", () => {
    const target = reveal(location.hash.slice(1));
    if (target) target.scrollIntoView();
  });
  reveal(location.hash.slice(1));                     // the page was opened at such a link
})();
