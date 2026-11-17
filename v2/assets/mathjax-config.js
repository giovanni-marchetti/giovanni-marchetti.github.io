// LaTeX settings shared by every page. Load this file before MathJax itself.
window.MathJax = {
  tex: {
    inlineMath: [["$", "$"], ["\\(", "\\)"]],
    displayMath: [["$$", "$$"], ["\\[", "\\]"]],
    tags: "ams",            // \begin{equation} is numbered; use \label{...} and \eqref{...}
    macros: {               // shared macros: add your own here
      R: "\\mathbb{R}",
      C: "\\mathbb{C}",
      K: "\\mathbb{K}",
      M: "\\mathcal{M}",
      Sym: "\\operatorname{Sym}",
      din: "d_{\\mathrm{in}}",    // write \K^{\din}, with braces
      dout: "d_{\\mathrm{out}}",
      dpar: "d_{\\mathrm{par}}",  // dimension of the parameter space: \Theta = \K^{\dpar}
      rank: "\\operatorname{rank}"
    }
  },
  chtml: {
    matchFontHeight: false,
    scale: 0.9              // size of math relative to the text (EB Garamond runs small)
  }
};
