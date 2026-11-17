// Collapsible sections (<details>): a link to an element inside a closed section, such as a citation pointing to an
// entry of the References, first opens that section, so that the browser can scroll to the element. The same happens
// when the page is opened at such an address, for example primer.html#pinkus1999approximation. No libraries.

(() => {
  "use strict";

  // Opens every closed <details> around the element with this id, and returns the element (or null).
  function reveal(id) {
    let target = null;
    try { target = id && document.getElementById(decodeURIComponent(id)); } catch { return null; }
    for (let d = target && target.closest("details"); d; d = d.parentElement && d.parentElement.closest("details"))
      d.open = true;
    return target;
  }

  // Runs before the browser follows the link.
  document.addEventListener("click", event => {
    const link = event.target.closest && event.target.closest('a[href^="#"]');
    if (link) reveal(link.getAttribute("href").slice(1));
  });
  window.addEventListener("hashchange", () => reveal(location.hash.slice(1)));
  if (location.hash) {
    const target = reveal(location.hash.slice(1));
    if (target) target.scrollIntoView();
  }
})();
