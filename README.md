This project uses Lean 4 and mathlib to formalize the main theorems of the paper
"Revisiting Separators in String Graphs, Region Intersection Graphs, and Induced-Minor-Free Graphs"
by Davies, Rzążewski, Spalding-Jamieson, and Walczak.

To compile, install lean and then simply run
```sh
lake build
```

The two main theorems are separately formalized in the `InducedMinorFreeSeparators` and `Padding` directories.
- The former shows that a `K_h^{(1)}`-forbidden-induced-minor graph with `m` edges admits separators of size `256 h √m · min(1280 log n, 625 h²)`.
- The latter shows that vertex-weighted region intersection graphs over `K_h`-minor-free graphs (for constant `h`) admit `(8192 h^2, 1/(1024h))`-padded decomposition schemes.

In addition, the following following LLM-assisted improvement is formalized, whose techniques appear in the full version:
- The improvement shows that a `K_h^{(1)}`-forbidden-induced-minor graph with `m` edges admits separators of size `O(log h) √m`.

This project's (original) formalizations were completed almost entirely by
the LLM-based tool [Aristotle](https://aristotle.harmonic.fun).
The improvement was formalized using GPT-5.6 with codex.

It is organized so that its definitions and main statements are easily human-verifiable, and these have been human-verified.
To verify them yourself, you need only read the following four files:
- `InducedMinorFreeSeparators/MainTheorem.lean`
- `InducedMinorFreeSeparators/Defs.lean`
- `Padding/Statements/RIGPaddedDecompDef.lean`
- `Padding/MainRegionIntersection.lean`
