import Tuza.Basic.Graph
import Tuza.Probability.Average

/-!
The random-cut cover selects W, noncrossing old edges, and each uncovered
triangle's new edges. When each triangle has at least two old edges, every
added edge is noncrossing.
-/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unoriented edge is noncrossing when its two colors agree. -/
def noncrossingEdge (χ : V → Bool) (e : Sym2 V) : Prop :=
  (Sym2.map χ e).IsDiag

instance (χ : V → Bool) : DecidablePred (noncrossingEdge χ) :=
  fun e => inferInstanceAs (Decidable (Sym2.map χ e).IsDiag)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem noncrossingEdge_pair (χ : V → Bool) (u v : V) :
    noncrossingEdge χ s(u, v) ↔ χ u = χ v := by
  simp [noncrossingEdge]

/-- The old edges selected before any uncovered triangles are considered. -/
def selectedOld (W O : Finset (Sym2 V)) (χ : V → Bool) : Finset (Sym2 V) :=
  W ∪ O.filter (noncrossingEdge χ)

/-- Add every non-old edge of every triangle that the selected old edges miss.
Using a union counts a repeated edge only once. -/
noncomputable def cutAddedEdges (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) :=
  (residual (trianglesOn A) (selectedOld W O χ)).biUnion (fun T => T \ O)

noncomputable def cutCover (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) := selectedOld W O χ ∪ cutAddedEdges A W O χ

@[simp] theorem mem_cutAddedEdges {A W O : Finset (Sym2 V)} {χ : V → Bool}
    {e : Sym2 V} :
    e ∈ cutAddedEdges A W O χ ↔
      ∃ T ∈ residual (trianglesOn A) (selectedOld W O χ), e ∈ T \ O := by
  classical
  simp [cutAddedEdges]

omit [Fintype V] in
/-- Every triangle has a noncrossing edge under a Boolean vertex coloring. -/
theorem IsTriangle.exists_noncrossing {T : Finset (Sym2 V)} (hT : IsTriangle T)
    (χ : V → Bool) : ∃ e ∈ T, noncrossingEdge χ e := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := hT
  have h : χ u = χ v ∨ χ u = χ w ∨ χ v = χ w := by
    cases χ u <;> cases χ v <;> cases χ w <;> decide
  rcases h with h | h | h
  · exact ⟨s(u, v), by simp, (noncrossingEdge_pair χ u v).mpr h⟩
  · exact ⟨s(u, w), by simp, (noncrossingEdge_pair χ u w).mpr h⟩
  · exact ⟨s(v, w), by simp, (noncrossingEdge_pair χ v w).mpr h⟩

omit [Fintype V] in
theorem selectedOld_subset_old {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (χ : V → Bool) : selectedOld W O χ ⊆ O := by
  exact union_subset hW (filter_subset _ _)

/-- A noncrossing edge of an uncovered triangle cannot be old. -/
theorem residual_noncrossing_not_old {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ))
    {e : Sym2 V} (he : e ∈ T) (hNC : noncrossingEdge χ e) : e ∉ O := by
  intro heO
  exact disjoint_left.mp (mem_residual.mp hT).2 he
    (mem_union_right _ (mem_filter.mpr ⟨heO, hNC⟩))

theorem residual_new_edges_nonempty {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ)) :
    (T \ O).Nonempty := by
  have htri := (mem_trianglesOn.mp (mem_residual.mp hT).1).1
  obtain ⟨e, he, hNC⟩ := htri.exists_noncrossing χ
  exact ⟨e, mem_sdiff.mpr ⟨he, residual_noncrossing_not_old hT he hNC⟩⟩

/-- The selected old edges and the uncovered triangles' new edges cover every triangle. -/
theorem cutCover_covers (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    IsCover (trianglesOn A) (cutCover A W O χ) := by
  apply cover_union_residual
  intro T hT
  obtain ⟨e, he⟩ := residual_new_edges_nonempty hT
  exact ⟨e, mem_inter.mpr ⟨(mem_sdiff.mp he).1,
    mem_cutAddedEdges.mpr ⟨T, hT, he⟩⟩⟩

theorem cutAddedEdges_subset {A W O : Finset (Sym2 V)} (χ : V → Bool) :
    cutAddedEdges A W O χ ⊆ A \ O := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  obtain ⟨heT, heO⟩ := mem_sdiff.mp heT
  exact mem_sdiff.mpr
    ⟨(mem_trianglesOn.mp (mem_residual.mp hT).1).2 heT, heO⟩

theorem cutCover_subset {A W O : Finset (Sym2 V)}
    (hW : W ⊆ O) (hO : O ⊆ A) (χ : V → Bool) :
    cutCover A W O χ ⊆ A := by
  exact union_subset ((selectedOld_subset_old hW χ).trans hO)
    ((cutAddedEdges_subset χ).trans sdiff_subset)

/-- There is only one possible new edge in a triangle with at least two old
edges, so every added edge equals its noncrossing edge. -/
theorem cutAddedEdges_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card) (χ : V → Bool)
    {e : Sym2 V} (he : e ∈ cutAddedEdges A W O χ) : noncrossingEdge χ e := by
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  have ht := (mem_residual.mp hT).1
  have htri := (mem_trianglesOn.mp ht).1
  obtain ⟨f, hf, hNC⟩ := htri.exists_noncrossing χ
  have hfnew : f ∈ T \ O :=
    mem_sdiff.mpr ⟨hf, residual_noncrossing_not_old hT hf hNC⟩
  have hcard : (T \ O).card ≤ 1 := by
    have hs := card_sdiff_add_card_inter T O
    have htcard := trianglesOn_card ht
    have ho := hOld T ht
    omega
  have hef : e = f := (card_le_one.mp hcard) e heT f hfnew
  exact hef ▸ hNC

theorem cutAddedEdges_inter_subset_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    cutAddedEdges A W O χ ∩ N ⊆ N.filter (noncrossingEdge χ) := by
  intro e he
  obtain ⟨heAdd, heN⟩ := mem_inter.mp he
  exact mem_filter.mpr ⟨heN, cutAddedEdges_noncrossing hOld χ heAdd⟩

/-- Every actual nonloop edge is noncrossing in exactly half of all cuts. -/
theorem noncrossingEdge_average (e : Sym2 V) (he : ¬ e.IsDiag) :
    bitAverage (fun χ => if noncrossingEdge χ e then (1 : ℚ) else 0) = 1 / 2 := by
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have huv : u ≠ v := fun h => he (Sym2.mk_isDiag_iff.mpr h)
  calc
    bitAverage (fun χ => if noncrossingEdge χ s(u, v) then (1 : ℚ) else 0) =
        bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) := by
      congr 1
      funext χ
      simp [sameColor]
    _ = 1 / 2 := sameColor_average u v huv

/-- The expected number of noncrossing edges is half the number of edges. -/
theorem noncrossingEdges_average (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
      (E.card : ℚ) / 2 := by
  calc
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
        ∑ e ∈ E, bitAverage (fun χ => if noncrossingEdge χ e then (1 : ℚ) else 0) := by
      unfold bitAverage
      simp_rw [natCast_card_filter]
      exact finiteAverage_finset_sum E _
    _ = ∑ _e ∈ E, (1 / 2 : ℚ) := by
      apply sum_congr rfl
      intro e he
      exact noncrossingEdge_average e (hE e he)
    _ = (E.card : ℚ) / 2 := by simp [div_eq_mul_inv]

omit [Fintype V] in
theorem selectedOld_eq_union_sdiff (W O : Finset (Sym2 V)) (χ : V → Bool) :
    selectedOld W O χ = W ∪ (O \ W).filter (noncrossingEdge χ) := by
  ext e
  simp only [selectedOld, mem_union, mem_filter, mem_sdiff]
  tauto

omit [Fintype V] in
theorem selectedOld_card (W O : Finset (Sym2 V)) (χ : V → Bool) :
    (selectedOld W O χ).card = W.card + ((O \ W).filter (noncrossingEdge χ)).card := by
  rw [selectedOld_eq_union_sdiff, card_union_of_disjoint]
  apply disjoint_left.mpr
  intro e heW heF
  exact (mem_sdiff.mp (mem_filter.mp heF).1).2 heW

/-- The expected cost of the selected old edges. -/
theorem selectedOld_average {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (hO : ∀ e ∈ O, ¬ e.IsDiag) :
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) =
      (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 := by
  calc
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) =
        (W.card : ℚ) + bitAverage
          (fun χ => (((O \ W).filter (noncrossingEdge χ)).card : ℚ)) := by
      simp_rw [selectedOld_card, Nat.cast_add]
      exact (finiteAverage_add _ _).trans
        (by rw [finiteAverage_const]; rfl)
    _ = (W.card : ℚ) + ((O \ W).card : ℚ) / 2 := by
      rw [noncrossingEdges_average (O \ W)
        (fun e he => hO e (mem_sdiff.mp he).1)]
    _ = (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 := by
      rw [card_sdiff_of_subset hW, Nat.cast_sub (card_le_card hW)]

theorem selectedOld_average_le {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (hO : ∀ e ∈ O, ¬ e.IsDiag) :
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) ≤
      (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 :=
  (selectedOld_average hW hO).le

/-- The nonloop hypothesis is automatic for a set of actual simple-graph edges. -/
theorem noncrossingGraphEdges_average (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : E ⊆ graphEdges G) :
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
      (E.card : ℚ) / 2 :=
  noncrossingEdges_average E
    (fun _ he => G.not_isDiag_of_mem_edgeSet (mem_graphEdges.mp (hE he)))

/-- The pointwise cover cost, separating added edges inside and outside `N`. -/
theorem cutCover_card_le {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    (cutCover A W O χ).card ≤ W.card +
      ((O \ W).filter (noncrossingEdge χ)).card +
      (N.filter (noncrossingEdge χ)).card + (cutAddedEdges A W O χ \ N).card := by
  have hi := card_le_card (cutAddedEdges_inter_subset_noncrossing (W := W) hOld N χ)
  have hs := card_inter_add_card_sdiff (cutAddedEdges A W O χ) N
  have hu := card_union_le (selectedOld W O χ) (cutAddedEdges A W O χ)
  rw [selectedOld_card] at hu
  change (selectedOld W O χ ∪ cutAddedEdges A W O χ).card ≤ _
  omega

/-- The same pointwise inequality in the indicator form consumed by finite
average linearity. -/
theorem cutCover_charge_le {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    ((cutCover A W O χ).card : ℚ) ≤ (W.card : ℚ) +
      (∑ e ∈ O \ W, if noncrossingEdge χ e then (1 : ℚ) else 0) +
      (∑ e ∈ N, if noncrossingEdge χ e then (1 : ℚ) else 0) +
      ((cutAddedEdges A W O χ \ N).card : ℚ) := by
  simp only [sum_boole]
  exact_mod_cast cutCover_card_le hOld N χ

end Tuza
