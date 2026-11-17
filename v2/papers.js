// The papers on the Literature page (literature.html), one entry per paper, after the tags that filter them.
//
// To add a paper, copy an entry, paste it anywhere in the list and change its fields. The page sorts the
// papers by the surname of the first author, then by year, so the order of the entries here does not matter.
//
//   id            Name of the entry, used in links: literature.html#kileel2019expressive. By convention, the
//                 surname of the first author, the year and the first word of the title, in lowercase.
//   authors       Full names, separated by commas.
//   title         Title of the paper.
//   venue         Journal or conference, or "Preprint".
//   year          Year of publication.
//   link          Page of the paper; for arXiv, its abstract page https://arxiv.org/abs/..., and otherwise its DOI,
//                 https://doi.org/..., if it has one.
//   topics        One or more of the topics in TAGS, below.
//   architecture  One or more of the architectures in TAGS, below.
//   activation    One or more of the activations in TAGS, below. Optional.
//
// Several values in one field are separated by commas. Each entry ends with a comma. Text goes between double
// quotes; inside it, a double quote is written \" and a backslash \\, so LaTeX is written like "$\\mathbb{R}^n$".

// The tags, in the rows and the order in which the page shows them above the list. A reader can select several;
// a paper is then shown if, in every row with a selected tag, it has at least one of the selected tags. Each row
// lists the values of one field of the papers (field), under a name (name), and the tags under each paper may be
// followed by a word (suffix: "Monomial activation"). Each tag has
//   name    Its name, as written in the papers (in any case).
//   about   What it covers, shown when the pointer rests on the tag. It is also the rule for tagging a paper.
//   primer  The id of the part of primer.html about it, if any. Not shown on the page at present.
// The topics follow the sections of the Primer. To add a tag, add a line to its row; a value that is in a paper but
// not here still gets a tag, at the end of its row, with a warning in the browser console. To remove a row, delete
// it: its field is then ignored.

const TAGS = [

{
  field: "topics",
  name: "Topic",
  tags: [
    { name: "Neuromanifolds", primer: "neuromanifolds",
      about: "The neuromanifold and the neurovariety themselves: their equations, semi-algebraic description and boundary." },
    { name: "Distance minimization", primer: "learning",
      about: "Learning as distance minimization over the neuromanifold: critical points of the loss, Euclidean distance degree." },
    { name: "Universal approximation", primer: "universal-approximation",
      about: "Which functions a model can express, and which architectures fill the ambient space." },
    { name: "Dimension and degree", primer: "sample-complexity",
      about: "The dimension and the degree of the neurovariety." },
    { name: "Sample complexity", primer: "sample-complexity",
      about: "How much data a model needs: covering numbers, generalization bounds." },
    { name: "Identifiability", primer: "identifiability",
      about: "The fibers of the parametrization map, and their relation to equivariance." },
    { name: "Singularities", primer: "singularities",
      about: "Singular points of the neuromanifold, subnetworks, implicit bias." },
    { name: "Learning dynamics", primer: "gradient-flow",
      about: "Gradient flow and gradient descent, the neural tangent kernel." },
  ],
},

{
  field: "architecture",
  name: "Architecture",
  tags: [
    { name: "General", primer: "def-algebraic-model",
      about: "Results for algebraic models in general, whatever the architecture." },
    { name: "MLP", primer: "ex-perceptrons",
      about: "Multilayer perceptrons." },
    { name: "CNN", primer: "ex-weight-sharing",
      about: "Convolutional networks, including group convolutions." },
    { name: "ResNet", primer: "ex-skip-connections",
      about: "Residual networks, with skip connections." },
    { name: "Equivariant", primer: "prop-equivariance-fibers",
      about: "Networks whose function, or whose layers, are equivariant under a group." },
    { name: "Attention",
      about: "Self-attention, as in transformers." },
  ],
},

{
  field: "activation",
  name: "Activation",
  suffix: "activation",
  tags: [
    { name: "Linear", primer: "ex-perceptrons",
      about: "Linear networks: the activation is the identity." },
    { name: "Monomial", primer: "ex-perceptrons",
      about: "Monomial activation, σ(t) = tʳ." },
    { name: "Polynomial",
      about: "General polynomial activations, rather than monomials." },
    { name: "Rational",
      about: "Rational activations." },
    { name: "General",
      about: "Activations that need not be polynomial." },
  ],
},

];

const PAPERS = [

{
  id: "achour2026riemannian",
  authors: "El Mehdi Achour, Kathlén Kohn, Holger Rauhut",
  title: "The Riemannian Geometry associated to Gradient Flows of Linear Convolutional Networks",
  venue: "International Conference on Artificial Intelligence and Statistics (AISTATS)",
  year: 2026,
  link: "https://arxiv.org/abs/2507.06367",
  topics: "Learning dynamics",
  architecture: "CNN",
  activation: "Linear",
},

{
  id: "akbari2026algebraic",
  authors: "Sepehr Akbari, Shahrzad Jamshidi",
  title: "Algebraic Expressivity Certificates for Shallow Polynomial Neural Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2609.28500",
  topics: "Neuromanifolds, Universal approximation",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "alexandr2026algebraic",
  authors: "Yulia Alexandr, Hao Duan, Guido Montúfar",
  title: "Algebraic Invariants of Lightning Self-Attention",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2604.15632",
  topics: "Neuromanifolds",
  architecture: "Attention",
},

{
  id: "alexandr2026robustness",
  authors: "Yulia Alexandr, Hao Duan, Guido Montúfar",
  title: "Robustness Verification of Polynomial Neural Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2602.06105",
  topics: "Distance minimization",
  architecture: "MLP, Attention",
  activation: "Monomial",
},

{
  id: "arjevani2026geometry",
  authors: "Yossi Arjevani, Joan Bruna, Joe Kileel, Elzbieta Polak, Matthew Trager",
  title: "Geometry and Optimization of Shallow Polynomial Networks",
  venue: "SIAM Journal on Applied Algebra and Geometry",
  year: 2026,
  link: "https://arxiv.org/abs/2501.06074",
  topics: "Neuromanifolds, Distance minimization",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "chang2026linear",
  authors: "Xiaotian Chang, Yacoub Hendi",
  title: "Linear Independence of Polynomial Compositions with Bounded Input Degree",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2610.20825",
  topics: "Identifiability",
  architecture: "MLP",
  activation: "Polynomial",
},

{
  id: "cheng2026quotient",
  authors: "Pengcheng Cheng",
  title: "Quotient Dynamics, Effective Curvature, and Implicit Bias in Positive Quadratic Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2607.25624",
  topics: "Learning dynamics",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "craciun2025linear",
  authors: "Alexandru Crăciun",
  title: "Linear Independence of Powers for Polynomials",
  venue: "Preprint",
  year: 2025,
  link: "https://arxiv.org/abs/2507.10163",
  topics: "Identifiability",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "dahlgren2026polynomial",
  authors: "Isabel Dahlgren, Giovanni Luca Marchetti, Kathlén Kohn",
  title: "Polynomial Residual Networks are Generically Identifiable",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2610.33738",
  topics: "Identifiability, Singularities",
  architecture: "ResNet",
  activation: "Polynomial",
},

{
  id: "dao2026minimal",
  authors: "Kevin Dao, Jose Israel Rodriguez",
  title: "Minimal Filling Architectures for Polynomial Neural Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2605.09609",
  topics: "Universal approximation, Dimension and degree",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "fefferman1994reconstructing",
  authors: "Charles Fefferman",
  title: "Reconstructing a neural net from its output",
  venue: "Revista Matemática Iberoamericana",
  year: 1994,
  link: "https://doi.org/10.4171/rmi/160",
  topics: "Identifiability",
  architecture: "MLP",
  activation: "General",
},

{
  id: "finkel2025activation",
  authors: "Bella Finkel, Jose Israel Rodriguez, Chenxi Wu, Thomas Yahl",
  title: "Activation degree thresholds and expressiveness of polynomial neural networks",
  venue: "Algebraic Statistics",
  year: 2025,
  link: "https://arxiv.org/abs/2408.04569",
  topics: "Dimension and degree, Identifiability",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "galley2026conservation",
  authors: "Jakob Galley, Vahid Shahverdi, Axel Flinth",
  title: "Conservation Laws from Data Symmetry in Neural Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2606.10913",
  topics: "Learning dynamics",
  architecture: "General, Attention",
  activation: "Linear, Polynomial",
},

{
  id: "graziani2025euclidean",
  authors: "Giacomo Graziani",
  title: "On the Euclidean Distance Degree of Quadratic Two-Neuron Neural Networks",
  venue: "Preprint",
  year: 2025,
  link: "https://arxiv.org/abs/2512.21016",
  topics: "Distance minimization",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "graziani2026euclidean",
  authors: "Giacomo Graziani",
  title: "On the Euclidean Distance Degree of Shallow Polynomial Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2601.16071",
  topics: "Distance minimization",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "grosdos2025algebraic",
  authors: "Alexandros Grosdos, Elina Robeva, Maksym Zubkov",
  title: "Algebraic geometry of rational neural networks",
  venue: "Preprint",
  year: 2025,
  link: "https://arxiv.org/abs/2509.11088",
  topics: "Neuromanifolds, Universal approximation, Dimension and degree",
  architecture: "MLP",
  activation: "Rational",
},

{
  id: "hendi2026geometry",
  authors: "Yacoub Hendi, Daniel Persson, Magdalena Larfors",
  title: "The Geometry of Polynomial Group Convolutional Neural Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2603.29566",
  topics: "Dimension and degree, Identifiability",
  architecture: "CNN, Equivariant",
  activation: "Monomial",
},

{
  id: "henry2025geometry",
  authors: "Nathan W. Henry, Giovanni Luca Marchetti, Kathlén Kohn",
  title: "Geometry of Lightning Self-Attention: Identifiability and Dimension",
  venue: "International Conference on Learning Representations (ICLR)",
  year: 2025,
  link: "https://arxiv.org/abs/2408.17221",
  topics: "Dimension and degree, Identifiability, Singularities",
  architecture: "Attention",
},

{
  id: "ibragimov2026landscape",
  authors: "Shokhrukh Ibragimov, Ilkhom Mukhammadiev, Diyora Salimova",
  title: "Landscape analysis for shallow neural networks: Complete classification of critical points for cubic activation and affine target functions",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2607.15173",
  topics: "Distance minimization",
  architecture: "MLP",
  activation: "Monomial",
},

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

{
  id: "kohn2022geometry",
  authors: "Kathlén Kohn, Thomas Merkh, Guido Montúfar, Matthew Trager",
  title: "Geometry of Linear Convolutional Networks",
  venue: "SIAM Journal on Applied Algebra and Geometry",
  year: 2022,
  link: "https://arxiv.org/abs/2108.01538",
  topics: "Neuromanifolds, Distance minimization, Learning dynamics",
  architecture: "CNN",
  activation: "Linear",
},

{
  id: "kohn2024function",
  authors: "Kathlén Kohn, Guido Montúfar, Vahid Shahverdi, Matthew Trager",
  title: "Function Space and Critical Points of Linear Convolutional Networks",
  venue: "SIAM Journal on Applied Algebra and Geometry",
  year: 2024,
  link: "https://arxiv.org/abs/2304.05752",
  topics: "Neuromanifolds, Distance minimization, Dimension and degree, Singularities",
  architecture: "CNN",
  activation: "Linear",
},

{
  id: "kohn2025geometry",
  authors: "Kathlén Kohn, Anna-Laura Sattelberger, Vahid Shahverdi",
  title: "Geometry of linear neural networks: equivariance and invariance under permutation groups",
  venue: "SIAM Journal on Matrix Analysis and Applications",
  year: 2025,
  link: "https://arxiv.org/abs/2309.13736",
  topics: "Neuromanifolds, Distance minimization, Dimension and degree, Singularities",
  architecture: "MLP, Equivariant",
  activation: "Linear",
},

{
  id: "kohn2026linear",
  authors: "Kathlén Kohn, Giovanni Luca Marchetti, Alex Massarenti, Massimiliano Mella",
  title: "Linear Independence of Polynomial Compositions and Identifiability of Deep Neural Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2608.27113",
  topics: "Identifiability",
  architecture: "MLP",
  activation: "Polynomial",
},

{
  id: "kohn2026singular",
  authors: "Kathlén Kohn, Giovanni Luca Marchetti, Farhan Shabir, Vahid Shahverdi, Weisheng Wang",
  title: "Singular Learning and Occam's Razor in Deep Monomial Networks",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2606.28464",
  topics: "Singularities, Learning dynamics",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "konda2026identifiability",
  authors: "Pranav Venkata Konda",
  title: "The Identifiability and Observability of Deep Normalized Attention",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2610.09620",
  topics: "Identifiability",
  architecture: "Attention",
},

{
  id: "kubjas2024geometry",
  authors: "Kaie Kubjas, Jiayi Li, Maximilian Wiesmann",
  title: "Geometry of Polynomial Neural Networks",
  venue: "Algebraic Statistics",
  year: 2024,
  link: "https://arxiv.org/abs/2402.00949",
  topics: "Neuromanifolds, Distance minimization, Dimension and degree",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "marchetti2025invitation",
  authors: "Giovanni Luca Marchetti, Vahid Shahverdi, Stefano Mereta, Matthew Trager, Kathlén Kohn",
  title: "Algebra Unveils Deep Learning – An Invitation to Neuroalgebraic Geometry",
  venue: "International Conference on Machine Learning (ICML)",
  year: 2025,
  link: "https://arxiv.org/abs/2501.18915",
  topics: "Neuromanifolds, Distance minimization, Universal approximation, Dimension and degree, Sample complexity, Identifiability, Singularities, Learning dynamics",
  architecture: "General, MLP, CNN, Attention",
  activation: "General",
},

{
  id: "marchetti2025critical",
  authors: "Giovanni Luca Marchetti, Erin Connelly, Paul Breiding, Kathlén Kohn",
  title: "Critical Points of Degenerate Metrics on Algebraic Varieties: A Tale of Overparametrization",
  venue: "Preprint",
  year: 2025,
  link: "https://arxiv.org/abs/2512.21029",
  topics: "Distance minimization",
  architecture: "General, MLP, Attention",
  activation: "General",
},

{
  id: "massarenti2025alexander",
  authors: "Alex Massarenti, Massimiliano Mella",
  title: "The Alexander-Hirschowitz theorem for neurovarieties",
  venue: "Preprint",
  year: 2025,
  link: "https://arxiv.org/abs/2511.19703",
  topics: "Dimension and degree, Identifiability",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "mody2025geometry",
  authors: "Param Mody, Maksym Zubkov",
  title: "Geometry of Rank Constraints in Shallow Polynomial Neural Networks",
  venue: "ICML Workshop on Methods and Opportunities at Small Scale (MOSS)",
  year: 2025,
  link: "https://openreview.net/forum?id=43cfYyiNiY",
  topics: "Distance minimization, Learning dynamics",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "nguyen2026parameter",
  authors: "Khang Nguyen, Guido Montúfar",
  title: "On Parameter Symmetries and Conservation Laws in Gradient Flow",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2609.34549",
  topics: "Identifiability, Learning dynamics",
  architecture: "MLP, Attention",
  activation: "Linear, Polynomial",
},

{
  id: "pardo2026erzeugungsgrad",
  authors: "Luis Miguel Pardo, Daniel Sebastián",
  title: "Erzeugungsgrad, VC-dimension and neural networks with rational activation function",
  venue: "Applicable Algebra in Engineering, Communication and Computing",
  year: 2026,
  link: "https://arxiv.org/abs/2504.11345",
  topics: "Dimension and degree, Sample complexity",
  architecture: "MLP",
  activation: "Rational",
},

{
  id: "ribot2026neural",
  authors: "Alvaro Ribot, Yulia Alexandr, Anna Seigal",
  title: "Do Neural Models Prefer Their Submodels?",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2610.28439",
  topics: "Distance minimization, Singularities",
  architecture: "MLP, CNN, Attention",
  activation: "Monomial, Polynomial, General",
},

{
  id: "shahverdi2025algebraic",
  authors: "Vahid Shahverdi",
  title: "Algebraic complexity and neurovariety of linear convolutional networks",
  venue: "Acta Universitatis Sapientiae, Mathematica",
  year: 2025,
  link: "https://arxiv.org/abs/2401.16613",
  topics: "Neuromanifolds, Distance minimization",
  architecture: "CNN",
  activation: "Linear",
},

{
  id: "shahverdi2025geometry",
  authors: "Vahid Shahverdi, Giovanni Luca Marchetti, Kathlén Kohn",
  title: "On the Geometry and Optimization of Polynomial Convolutional Networks",
  venue: "International Conference on Artificial Intelligence and Statistics (AISTATS)",
  year: 2025,
  link: "https://arxiv.org/abs/2410.00722",
  topics: "Distance minimization, Dimension and degree, Identifiability, Singularities",
  architecture: "CNN",
  activation: "Monomial",
},

{
  id: "shahverdi2026identifiable",
  authors: "Vahid Shahverdi, Giovanni Luca Marchetti, Georg Bökman, Kathlén Kohn",
  title: "Identifiable Equivariant Networks are Layerwise Equivariant",
  venue: "International Conference on Machine Learning (ICML)",
  year: 2026,
  link: "https://arxiv.org/abs/2601.21645",
  topics: "Identifiability",
  architecture: "General, Equivariant",
  activation: "General",
},

{
  id: "shahverdi2026learning",
  authors: "Vahid Shahverdi, Giovanni Luca Marchetti, Kathlén Kohn",
  title: "Learning on a Razor's Edge: Identifiability and Singularity of Polynomial Neural Networks",
  venue: "International Conference on Learning Representations (ICLR)",
  year: 2026,
  link: "https://arxiv.org/abs/2505.11846",
  topics: "Distance minimization, Dimension and degree, Identifiability, Singularities",
  architecture: "MLP, CNN",
  activation: "Polynomial",
},

{
  id: "trager2020pure",
  authors: "Matthew Trager, Kathlén Kohn, Joan Bruna",
  title: "Pure and Spurious Critical Points: a Geometric Study of Linear Networks",
  venue: "International Conference on Learning Representations (ICLR)",
  year: 2020,
  link: "https://arxiv.org/abs/1910.01671",
  topics: "Distance minimization",
  architecture: "MLP",
  activation: "Linear",
},

{
  id: "usevich2025identifiability",
  authors: "Konstantin Usevich, Ricardo Borsoi, Clara Dérand, Marianne Clausel",
  title: "Identifiability of Deep Polynomial Neural Networks",
  venue: "Advances in Neural Information Processing Systems (NeurIPS)",
  year: 2025,
  link: "https://arxiv.org/abs/2506.17093",
  topics: "Dimension and degree, Identifiability",
  architecture: "MLP",
  activation: "Monomial",
},

{
  id: "yuan2026grassmann",
  authors: "Hongyu Yuan, Huaiqing Zuo",
  title: "Grassmann–Plücker Parametrization of Convolutional Filter Subspaces: Regularity and Closed Embeddings",
  venue: "Preprint",
  year: 2026,
  link: "https://arxiv.org/abs/2609.03361",
  topics: "Neuromanifolds, Identifiability",
  architecture: "CNN",
  activation: "Linear",
},

{
  id: "zhang2025covering",
  authors: "Yifan Zhang, Joe Kileel",
  title: "Covering Number of Real Algebraic Varieties and Beyond: Improved Bounds and Applications",
  venue: "Foundations of Computational Mathematics",
  year: 2025,
  link: "https://arxiv.org/abs/2311.05116",
  topics: "Sample complexity",
  architecture: "General, MLP, CNN",
  activation: "Rational, General",
},

{
  id: "zubkov2025expressivity",
  authors: "Maksym Zubkov, Carol Wu, Shiwei Yang, Param Mody, Yifei Chen",
  title: "Expressivity of Shallow Neural Networks Over Finite Fields",
  venue: "Preprint",
  year: 2025,
  link: "https://openreview.net/forum?id=tfGuvCp50e",
  topics: "Universal approximation",
  architecture: "MLP",
  activation: "Monomial",
},

];
