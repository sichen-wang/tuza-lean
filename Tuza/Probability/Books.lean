import Tuza.Books.Cover
import Tuza.Probability.Cut
import Tuza.Construction.Types

/-! The expected cost of adding opposite edges to a random-cut cover. -/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {I : Type*} [Fintype I]

namespace Book

/-- Only a two-page book can contribute an opposite edge to a cut cover. -/
def cutEvent (b : Book V) (χ : V → Bool) : Prop :=
  match b with
  | .double u v x y _ => bookEvent u v x y χ
  | _ => False

instance (b : Book V) : DecidablePred b.cutEvent := by
  intro χ
  cases b <;> unfold cutEvent <;> infer_instance

theorem cutEvent_average (b : Book V) :
    bitAverage (fun χ => if b.cutEvent χ then (1 : ℚ) else 0) ≤ 3 / 8 := by
  cases b with
  | single u v x h => norm_num [cutEvent, bitAverage, finiteAverage_const]
  | double u v x y h =>
    apply le_of_eq
    apply bookEvent_average <;> simp_all [List.nodup_cons]
  | triple u v x y z h => norm_num [cutEvent, bitAverage, finiteAverage_const]

end Book

/-- Books whose opposite edge is an actual new edge outside the packing. -/
noncomputable def oppositeBooks (A O N : Finset (Sym2 V)) (books : I → Book V) : Finset I := by
  classical
  exact univ.filter (fun i => ∃ e, (books i).opposite = some e ∧ e ∈ A \ O ∧ e ∉ N)

omit [Fintype V] in
@[simp] theorem mem_oppositeBooks {A O N : Finset (Sym2 V)} {books : I → Book V} {i : I} :
    i ∈ oppositeBooks A O N books ↔
      ∃ e, (books i).opposite = some e ∧ e ∈ A \ O ∧ e ∉ N := by
  classical
  simp [oppositeBooks]

/-- Every added edge outside N comes from a two-page book whose local
cut event occurs. The witness is derived from the actual uncovered triangle. -/
theorem cutAddedEdges_book_witness {A W O N : Finset (Sym2 V)} (books : I → Book V)
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (hNO : Disjoint N O)
    (hspine : ∀ i, (books i).spine ∈ N)
    (hblue : ∀ i U, U ∈ (books i).pages → U \ {(books i).spine} ⊆ O)
    (hsingle : ∀ i, (books i).pages.card = 1 →
      ∀ U ∈ (books i).pages, U ∩ O ⊆ W)
    (hchoice : Books.EveryChoiceMeets (typeFamily A O 2) (fun i => (books i).pages))
    (χ : V → Bool) {e : Sym2 V} (he : e ∈ cutAddedEdges A W O χ \ N) :
    ∃ i ∈ oppositeBooks A O N books, (books i).opposite = some e ∧ (books i).cutEvent χ := by
  obtain ⟨heAdd, heN⟩ := mem_sdiff.mp he
  obtain ⟨T, hT, heNew⟩ := mem_cutAddedEdges.mp heAdd
  have hactual := (mem_residual.mp hT).1
  have htri := (mem_trianglesOn.mp hactual).1
  have htype := new_edge_forces_typeTwo hactual (hOld T hactual) heNew
  have hnewCard : (T \ O).card ≤ 1 := by
    have hc := trianglesOn_card hactual
    have ho := hOld T hactual
    have hp := card_sdiff_add_card_inter T O
    omega
  have hdisN : Disjoint T N := by
    apply disjoint_left.mpr
    intro f hfT hfN
    have hfO : f ∉ O := fun hf => disjoint_left.mp hNO hfN hf
    have hfe := card_le_one.mp hnewCard f (mem_sdiff.mpr ⟨hfT, hfO⟩) e heNew
    exact heN (hfe ▸ hfN)
  obtain ⟨i, hi⟩ := Books.exists_book_all_pages_meet hchoice htype
  have hnotspine : (books i).spine ∉ T :=
    fun hm => disjoint_left.mp hdisN hm (hspine i)
  have hmeet : ∀ U ∈ (books i).pages, (T ∩ U).Nonempty := by
    intro U hU
    obtain ⟨f, hfT, hfU⟩ := not_disjoint_iff.mp (hi U hU)
    exact ⟨f, mem_inter.mpr ⟨hfT, hfU⟩⟩
  have hmemberOld : ∀ f ∈ T, ∀ U ∈ (books i).pages, f ∈ U → f ∈ O := by
    intro f hfT U hU hfU
    apply hblue i U hU
    exact mem_sdiff.mpr ⟨hfU, fun hf => hnotspine (mem_singleton.mp hf ▸ hfT)⟩
  have heNC := cutAddedEdges_noncrossing hOld χ heAdd
  have heA : e ∈ A \ O := cutAddedEdges_subset χ heAdd
  generalize hb : books i = b at hnotspine hmeet hmemberOld
  cases b with
  | single u v x hv =>
    obtain ⟨f, hf⟩ := hmeet (triangleEdges u v x) (by simp [Book.pages])
    obtain ⟨hfT, hfU⟩ := mem_inter.mp hf
    have hfOld := hmemberOld f hfT (triangleEdges u v x) (by simp [Book.pages]) hfU
    have hfW := hsingle i (by simp [hb, Book.pages]) (triangleEdges u v x)
      (by simp [hb, Book.pages]) (mem_inter.mpr ⟨hfU, hfOld⟩)
    exact False.elim (disjoint_left.mp (mem_residual.mp hT).2 hfT (mem_union_left _ hfW))
  | triple u v x y z hv =>
    have hs := three_page_spine htri hv
      (hmeet (triangleEdges u v x) (by simp [Book.pages]))
      (hmeet (triangleEdges u v y) (by simp [Book.pages]))
      (hmeet (triangleEdges u v z) (by simp [Book.pages]))
    exact False.elim (hnotspine hs)
  | double u v x y hv =>
    have hn : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
      simpa [List.nodup_cons, and_assoc] using hv
    obtain ⟨huv, hux, huy, hvx, hvy, hxy⟩ := hn
    have hshape := two_page_triangle htri hv hnotspine
      (hmeet (triangleEdges u v x) (by simp [Book.pages]))
      (hmeet (triangleEdges u v y) (by simp [Book.pages]))
    have huxOld : s(u, x) ∈ O := hblue i (triangleEdges u v x)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, hvx.symm, huv])
    have hvxOld : s(v, x) ∈ O := hblue i (triangleEdges u v x)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, hux.symm, huv.symm])
    have huyOld : s(u, y) ∈ O := hblue i (triangleEdges u v y)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, hvy.symm, huv])
    have hvyOld : s(v, y) ∈ O := hblue i (triangleEdges u v y)
      (by simp [hb, Book.pages]) (by simp [hb, Book.spine, huy.symm, huv.symm])
    have hexy : e = s(x, y) := by
      obtain ⟨heT, heO⟩ := mem_sdiff.mp heNew
      rcases hshape with hshape | hshape <;> rw [hshape] at heT <;>
        simp only [mem_triangleEdges] at heT
      · rcases heT with rfl | rfl | heT
        · exact False.elim (heO huxOld)
        · exact False.elim (heO huyOld)
        · exact heT
      · rcases heT with rfl | rfl | heT
        · exact False.elim (heO hvxOld)
        · exact False.elim (heO hvyOld)
        · exact heT
    have hop : (books i).opposite = some e := by simp [hb, hexy]
    refine ⟨i, mem_oppositeBooks.mpr ⟨e, hop, heA, heN⟩, hop, ?_⟩
    rw [hb]
    change χ x = χ y ∧ (χ u ≠ χ x ∨ χ v ≠ χ x)
    refine ⟨(noncrossingEdge_pair χ x y).mp (hexy ▸ heNC), ?_⟩
    rcases hshape with hshape | hshape
    · left
      intro hh
      exact residual_noncrossing_not_old hT
        (by simp [hshape] : s(u, x) ∈ T)
        ((noncrossingEdge_pair χ u x).mpr hh) huxOld
    · right
      intro hh
      exact residual_noncrossing_not_old hT
        (by simp [hshape] : s(v, x) ∈ T)
        ((noncrossingEdge_pair χ v x).mpr hh) hvxOld

omit [Fintype V] [Fintype I] in
/-- Each book contributes at most one opposite edge, so the union has at most
as many edges as there are books whose cut events occur. -/
theorem card_le_book_events (books : I → Book V) (J : Finset I)
    (D : Finset (Sym2 V)) (χ : V → Bool)
    (hw : ∀ e ∈ D, ∃ i ∈ J, (books i).opposite = some e ∧ (books i).cutEvent χ) :
    D.card ≤ (J.filter (fun i => (books i).cutEvent χ)).card := by
  classical
  let K := J.filter (fun i => (books i).cutEvent χ)
  have hsub : D ⊆ K.biUnion (fun i => (books i).opposite.toFinset) := by
    intro e he
    obtain ⟨i, hi, hop, hev⟩ := hw e he
    apply mem_biUnion.mpr
    exact ⟨i, mem_filter.mpr ⟨hi, hev⟩, by simp [hop]⟩
  calc
    D.card ≤ (K.biUnion (fun i => (books i).opposite.toFinset)).card := card_le_card hsub
    _ ≤ ∑ i ∈ K, (books i).opposite.toFinset.card := card_biUnion_le
    _ ≤ ∑ _i ∈ K, 1 := by
      apply sum_le_sum
      intro i _
      cases (books i).opposite <;> simp
    _ = K.card := by simp

omit [Fintype I] in
theorem book_events_average_le (books : I → Book V) (J : Finset I) :
    bitAverage (fun χ => ((J.filter (fun i => (books i).cutEvent χ)).card : ℚ))
      ≤ 3 * (J.card : ℚ) / 8 := by
  classical
  calc
    bitAverage (fun χ => ((J.filter (fun i => (books i).cutEvent χ)).card : ℚ)) =
        ∑ i ∈ J, bitAverage (fun χ => if (books i).cutEvent χ then (1 : ℚ) else 0) := by
      unfold bitAverage
      simp_rw [natCast_card_filter]
      exact finiteAverage_finset_sum J _
    _ ≤ ∑ _i ∈ J, (3 / 8 : ℚ) :=
      sum_le_sum (fun i _ => (books i).cutEvent_average)
    _ = 3 * (J.card : ℚ) / 8 := by simp; ring

/-- The random-cover bound obtained by averaging, with denominators cleared. -/
theorem random_book_cover {A W O N : Finset (Sym2 V)} (books : I → Book V)
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (hNO : Disjoint N O) (hW : W ⊆ O)
    (hOdiag : ∀ e ∈ O, ¬ e.IsDiag) (hNdiag : ∀ e ∈ N, ¬ e.IsDiag)
    (hspine : ∀ i, (books i).spine ∈ N)
    (hblue : ∀ i U, U ∈ (books i).pages → U \ {(books i).spine} ⊆ O)
    (hsingle : ∀ i, (books i).pages.card = 1 →
      ∀ U ∈ (books i).pages, U ∩ O ⊆ W)
    (hchoice : Books.EveryChoiceMeets (typeFamily A O 2) (fun i => (books i).pages)) :
    8 * transversalNumber (trianglesOn A) ≤
      4 * O.card + 4 * W.card + 4 * N.card + 3 * (oppositeBooks A O N books).card := by
  classical
  let J := oppositeBooks A O N books
  have hout (χ : V → Bool) : (cutAddedEdges A W O χ \ N).card ≤
      (J.filter (fun i => (books i).cutEvent χ)).card :=
    card_le_book_events books J _ χ (fun _ he =>
      cutAddedEdges_book_witness books hOld hNO hspine hblue hsingle hchoice χ he)
  have hpoint (χ : V → Bool) : ((cutCover A W O χ).card : ℚ) ≤
      ((selectedOld W O χ).card : ℚ) + ((N.filter (noncrossingEdge χ)).card : ℚ) +
        ((J.filter (fun i => (books i).cutEvent χ)).card : ℚ) := by
    have hc := cutCover_card_le (W := W) hOld N χ
    rw [← selectedOld_card] at hc
    exact_mod_cast hc.trans (Nat.add_le_add_left (hout χ) _)
  have havg := finiteAverage_mono _ _ hpoint
  rw [finiteAverage_add, finiteAverage_add] at havg
  change bitAverage _ ≤ bitAverage _ + bitAverage _ + bitAverage _ at havg
  rw [selectedOld_average hW hOdiag, noncrossingEdges_average N hNdiag] at havg
  have hevent := book_events_average_le books J
  obtain ⟨χ, hχ⟩ := exists_le_finiteAverage
    (fun χ : V → Bool => ((cutCover A W O χ).card : ℚ))
  have hcover : (transversalNumber (trianglesOn A) : ℚ) ≤ (cutCover A W O χ).card := by
    exact_mod_cast (cutCover_covers A W O χ).number_le
  have hfinal : (8 : ℚ) * transversalNumber (trianglesOn A) ≤
      4 * O.card + 4 * W.card + 4 * N.card + 3 * J.card := by
    change _ ≤ bitAverage _ at hχ
    linarith
  exact_mod_cast hfinal

end Tuza
