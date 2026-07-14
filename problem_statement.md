# Problem statement

## The model

A layer has `k` causal softmax-attention heads. For an input matrix `X`, head `a` in layer `l` has a value matrix `Vₗₐ` and attention matrix `Aₗₐ`; the layer output is the sum

```text
Σₐ Vₗₐ X softmax_causal(Xᵀ Aₗₐ X).
```

There is no additive copy of `X`: this is the no-skip architecture. A depth-`L` transformer is the composition of `L` such layers.

## The identifiability question

Suppose two parameter tuples `θ` and `θ′` produce the same output on every input of sequence length `r + 1`. Must their matrices agree?

Literal agreement is impossible because the realization has built-in symmetries. Heads may be reordered independently inside each layer. In addition, invertible changes of basis can be inserted at interfaces between adjacent layers, with compensating transformations on the surrounding attention and value matrices. The endpoint gauges are fixed to the identity so this chain is normalized.

The right question is therefore whether these obvious symmetries account for every ambiguity.

## Formal answer

Fix `n, k, r, d : ℕ` with

```text
1 ≤ k,
2 ≤ r,
max 2 (k * (n + 2)) ≤ d.
```

The Lean theorem constructs an explicit exceptional set `N` in the parameter space of `(n + 1)`-layer networks and proves:

1. `N` has Lebesgue measure zero.
2. If the target `θ′` is outside `N` and `θ` realizes the same transformer globally, there is a layerwise target-to-source head permutation and a boundary-normalized interface gauge chain relating their matrices.
3. That complete permutation/gauge matching is unique.
4. Conversely, applying any permitted permutation and gauge chain leaves the transformer unchanged.
5. Hence the entire generic realization fiber is exactly the permutation–gauge orbit, and its orbit parametrization is injective.

At factor level, under the stated full-rank assumptions, equal realizations also determine the individual factors up to the corresponding inner factorization gauges.

## What “generic” means here

Genericity is not assumed informally. The development builds polynomial certificates for the required regularity conditions, packages their zero loci into a recursive exceptional set, and proves that this set is null. Thus the theorem gives a concrete measure-theoretic statement rather than merely saying that the claim holds for “almost all” parameters.
