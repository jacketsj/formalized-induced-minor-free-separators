import InducedMinorFreeSeparators.ConcurrentFlowProof.LLL

/-!
# Symmetric Lovász Local Lemma

The symmetric LLL is now proved in `RequestProject.LLL` as
`lovasz_local_lemma_symmetric`. See that file for the full
measure-theoretic development including:

- `LopsidependenceCondition` — the lopsidependence condition
- `lovasz_local_lemma` — the asymmetric LLL
- `lovasz_local_lemma_pos` — positivity of the avoiding probability
- `lovasz_local_lemma_symmetric` — the symmetric LLL with condition `4p(d+1) ≤ 1`

The old finite-product-space formulation is no longer needed.
-/
