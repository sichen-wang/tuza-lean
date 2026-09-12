import Tuza.Construction.FirstCover
import Tuza.Construction.BookCover
import Tuza.Construction.ColoredCover
import Tuza.Basic.Graph
import Tuza.Construction.RandomCover

/-! Four covers of the same graph give the bound 165/59. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

theorem first_cover :
    transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card :=
  FirstCover.transversalNumber_add_typeOne_packing_le c.initial_maximum c.first_maximum.1

/-- The four estimates for the same choices of P, A, P', Q and Q1, using
the paper's count h of private red pages. -/
theorem four_covers (r : RefinedConstruction c) :
    (transversalNumber (trianglesOn edges) + c.first.card ≤ 3 * c.initial.card) ∧
    (8 * transversalNumber (trianglesOn edges) + 8 * r.second.card ≤
      12 * c.initial.card + 20 * c.first.card + 12 * c.typeTwo.card +
        3 * (privateRedPages c.specialFamily c.newEdges r.second).card) ∧
    (transversalNumber (trianglesOn edges) + r.second.card + r.third.card ≤
      3 * c.initial.card) ∧
    (4 * transversalNumber (trianglesOn edges) + 4 * c.typeTwo.card +
      (privateRedPages c.specialFamily c.newEdges r.second).card ≤
      12 * c.initial.card + 9 * r.second.card + 6 * r.third.card) :=
  ⟨c.first_cover, TwoLayer.random_cover c r.second_maximum.1, c.full_book_cover r,
    c.fourth_cover r.second_maximum r.third_maximum⟩

theorem bound_with_residual (r : RefinedConstruction c) :
    59 * transversalNumber (trianglesOn edges) + r.third.card ≤ 165 * c.initial.card := by
  obtain ⟨hfirst, hcut, hbooks, hcolored⟩ := c.four_covers r
  exact four_bounds_arithmetic hfirst hcut hbooks hcolored

end Construction

/-- The 165/59 bound for the triangle family of any finite edge set. -/
theorem triangles_bound (edges : Finset (Sym2 V)) :
    59 * transversalNumber (trianglesOn edges) ≤ 165 * packingNumber (trianglesOn edges) := by
  obtain ⟨c⟩ := exists_construction edges
  obtain ⟨r⟩ := exists_refinedConstruction c
  have h := c.bound_with_residual r
  rw [c.initial_maximum.card_eq] at h
  omega

/-- The main theorem for a finite simple graph, with denominators cleared. -/
theorem tuza_bound_nat (G : SimpleGraph V) : 59 * tau G ≤ 165 * nu G :=
  triangles_bound (graphEdges G)

/-- The main theorem in rational form. -/
theorem tuza_bound (G : SimpleGraph V) : (tau G : ℚ) ≤ (165 / 59 : ℚ) * nu G := by
  have h : (59 : ℚ) * tau G ≤ 165 * nu G := by exact_mod_cast tuza_bound_nat G
  linarith

/-- An equivalent concrete graph-edge transversal, stated directly in terms
of every triple of adjacent vertices. -/
theorem exists_small_triangle_transversal (G : SimpleGraph V) :
    ∃ C : Finset (Sym2 V), C ⊆ graphEdges G ∧
      (∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C) ∧
      59 * C.card ≤ 165 * nu G := by
  obtain ⟨C, hsub, hcover, hcard⟩ := exists_graph_minimumCover G
  exact ⟨C, hsub, (graph_cover_iff_adj G C).mp hcover, hcard.symm ▸ tuza_bound_nat G⟩

end Tuza
