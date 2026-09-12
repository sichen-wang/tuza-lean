# A Bound Below 2.8 for Tuza's Conjecture

A Lean 4 formalization of

$$
\tau(G) \le \tfrac{165}{59}\,\nu(G)
$$

for every finite simple graph $G$, where $\nu(G)$ is the maximum number of edge-disjoint triangles and $\tau(G)$ the minimum number of edges meeting every triangle, following the paper *A Bound Below 2.8 for Tuza's Conjecture*. All packings, transversals, and finite averages are constructed in Lean, and the proof depends on no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

## Build

Lean and Mathlib are pinned to `v4.32.0` by `lean-toolchain` and `lake-manifest.json`. With [elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get          # precompiled Mathlib
lake build                  # compile the proof; warnings are errors
lake env leanchecker Tuza   # replay every proof in the kernel
```

The kernel replay uses a few gigabytes of memory; `LEAN_NUM_THREADS=2` keeps it modest. To list the axioms behind the main theorem:

```sh
printf 'import Tuza\n#print axioms Tuza.tuza_bound\n' | lake env lean --stdin
```

## Main theorems

In [`Tuza/Main.lean`](Tuza/Main.lean), namespace `Tuza`:

- `tuza_bound_nat`: $59\,\tau(G) \le 165\,\nu(G)$;
- `tuza_bound`: $\tau(G) \le \frac{165}{59}\,\nu(G)$ in $\mathbb{Q}$;
- `exists_small_triangle_transversal`: an explicit set $C$ of edges of $G$ meeting every triangle, with $59\,|C| \le 165\,\nu(G)$.

Here $\tau$ and $\nu$ (`tau` and `nu` in [`Tuza/Basic/Graph.lean`](Tuza/Basic/Graph.lean)) are defined for Mathlib's `SimpleGraph`, and a triangle is identified with its set of three edges.

## Layout

| Directory | Contents |
| --- | --- |
| `Tuza/Basic` | packings and transversals of finite families, red and blue edges, triangle geometry, graphs, the final arithmetic |
| `Tuza/Books` | books and the book cover, Lemma 2.2 |
| `Tuza/Colored` | the family of all triangles with one red edge, the exchange (Lemma 2.1), the two colored bounds (Lemma 2.3) |
| `Tuza/Probability` | finite averages and the random-cut cover |
| `Tuza/Construction` | Haxell's packings and the four transversals, inequalities (3) to (6) |

## Correspondence with the paper

| Paper | Lean |
| --- | --- |
| Lemma 2.1 | `unique_residual_triangle` |
| Lemma 2.2 | `Book.meets_cover`, `exists_cover_of_small_common_spine_books` |
| Lemma 2.3, bounds (1) and (2) | `colored_bound`, `colored_refined` |
| inequality (3) | `Construction.first_cover` |
| inequality (4) | `TwoLayer.random_cover` |
| inequality (5) | `Construction.full_book_cover` |
| inequality (6) | `Construction.fourth_cover` |
| the combination | `Construction.bound_with_residual` |

The fields `initial`, `first`, and `rest` of `Construction` are $P$, $A$, and $P'$; `typeTwo` and `specialFamily` are $B^*$ and $\mathcal{S}$; `RefinedConstruction.second` and `.third` are $Q$ and $Q_1$; `privateRedPages` counts $h$.

## License

MIT, see [LICENSE](LICENSE).
