This project uses Lean 4 and mathlib to formalize the two main theorems of the paper
"Revisiting Separators in String Graphs, Region-Intersection Graphs, and Induced-Minor-Free Graphs"
by Davies, Rzążewski, Spalding-Jamieson, and Walczak.

To compile, insteall lean and then simply run
```sh
lake build
```

The two main theorems are separately formalized in the `InducedMinorFreeSeparators` and `Padding` directories.
- The former shows that a `K_h^{(1)}`-forbidden-induced-minor graph with `m` edges admits separators of size `256 h √m · min(1280 log n, 625 h²)`.
- The latter shows that vertex-weighted region-intersection graphs over `K_h`-minor-free graphs (for constant `h`) admit `(8192 h^2, 1/(1024h))`-padded decomposition schemes.


This project's formalizations were completed almost entirely by
the LLM-based tool [Aristotle](https://aristotle.harmonic.fun).

It is organized so that its definitions and main statements are easily human-verifiable, and these have been human-verified.
To verify them yourself, you need only read the following four files:
- `InducedMinorFreeSeparators/MainTheorem.lean`
- `InducedMinorFreeSeparators/Defs.lean`
- `Padding/Statements/RIGPaddedDecompDef.lean`
- `Padding/MainRegionIntersection.lean`
