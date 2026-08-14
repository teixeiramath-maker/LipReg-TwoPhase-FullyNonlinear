# Blueprint — Lipschitz2

The proof decomposition — one `## ` section per node. Lea co-authors this as it plans and formalizes, and you can edit it too. Each node has a short header then a prose statement:

```
## continuous_sq
- kind: lemma                # definition | lemma | theorem
- lean: `Lea.Lipschitz2.continuous_sq`   # the Lean decl, once it exists
- uses: tendsto_iff_eps      # keys of the nodes this one depends on

The function x ↦ x² is continuous in the ε–δ sense.
```

Add your first node below.

## lemcurvedplanarbarriers
- kind: theorem
- lean: `Lea.Lipschitz2.lemcurvedplanarbarriers`
- uses: StructuralDataAndNotation

The Pucci/profile pointwise estimates for strengthened and weakened planar profiles yield strict lower and upper comparisons under convex and concave bending, with the universal choice `κ₀ = λ / (8Λ)`.
