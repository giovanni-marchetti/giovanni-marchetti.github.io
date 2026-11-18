// Buttons that change a figure, such as the network in the section "Examples" of the Primer. Clicking a button with
// data-toggle="x" inside a <figure> presses or releases it (aria-pressed) and sets or removes the attribute data-x of
// the figure, so that CSS can show and hide parts of the figure while the button is pressed (see .mlp-figure in
// assets/style.css). No libraries.

(() => {
  "use strict";

  document.querySelectorAll("figure button[data-toggle]").forEach(button => {
    const figure = button.closest("figure");
    button.addEventListener("click", () => {
      const on = button.getAttribute("aria-pressed") !== "true";
      button.setAttribute("aria-pressed", String(on));
      figure.toggleAttribute("data-" + button.dataset.toggle, on);
    });
  });
})();
