This project uses Lean 4 and mathlib to formalize the two main theorems of the paper
"Revisiting Separators in String Graphs, Region-Intersection Graphs, and Induced-Minor-Free Graphs"
by Davies, Rzążewski, Spalding-Jamieson, and Walczak.

The two main theorems are separately formalized in the `InducedMinorFreeSeparators` and `Padding` directories.
- The former shows that forbidden-induced-minor graphs with `m` edges admit separators of size `O(c_H * sqrt(m))`, for some constant `c_H` depending only on `H`.  
- The latter shows that vertex-weighted region-intersection graphs over `K_h`-minor-free graphs (for constant `h`) have constant padding parameter.  
See the paper for the precise dependencies on the parameters.


This project's formalizations were completed almost entirely by
the LLM-based tool [Aristotle](https://aristotle.harmonic.fun).

It is organized so that its definitions and main statements are easily human-verifiable, and these have been human-verified.
To verify them yourself, you need only read the following four files:
- `InducedMinorFreeSeparators/MainTheorem.lean`
- `InducedMinorFreeSeparators/Defs.lean`
- `Padding/Statements/RIGPaddedDecompDef.lean`
- `Padding/MainRegionIntersection.lean`

To build yourself, simply run
```
lake build
```
