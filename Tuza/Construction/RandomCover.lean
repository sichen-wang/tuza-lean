import Tuza.Construction.OppositeEdges

/-! The two-layer random cover: equation (4). -/

namespace Tuza
namespace TwoLayer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {edges : Finset (Sym2 V)} (c : Construction edges)
variable {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q)

include hQ in
private theorem residual_packing :
    IsPacking (residual (typeFamily c.remainingEdges c.old 2)
      (blueEdges (c.remainingEdges \ c.old) c.typeTwo)) Q :=
  hQ.mono_family c.specialFamily_subset_typeTwo_residual

/-- The cut uses only the type-two packing and its second pages. -/
noncomputable def pages (Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ c.typeTwo}) :=
  Layered.twoLayerPages (c.remainingEdges \ c.old) c.typeTwo Q p

include hQ in
theorem pages_subset (p : {T // T ∈ c.typeTwo}) :
    pages c Q p ⊆ typeFamily c.remainingEdges c.old 2 :=
  Layered.pages_subset_family c.typeTwo_maximum (residual_packing c hQ) p

include hQ in
theorem pages_card_le_two (p : {T // T ∈ c.typeTwo}) :
    (pages c Q p).card ≤ 2 := by
  have hc := Layered.children_card_le_one (typeTwo_colored c.remainingEdges c.old)
    (residual_packing c hQ) p.val
  have hi := card_insert_le p.val (Layered.children (c.remainingEdges \ c.old) Q p.val)
  change (insert p.val (Layered.children (c.remainingEdges \ c.old) Q p.val)).card ≤ 2
  omega

theorem pages_common_spine (p : {T // T ∈ c.typeTwo}) :
    ∀ T ∈ pages c Q p, Construction.typeTwoSpine p ∈ T := by
  intro T hT
  have hs := Construction.typeTwoSpine_mem p
  rcases Layered.mem_twoLayerPages.mp hT with rfl | ⟨_, hred⟩
  · exact (mem_inter.mp hs).1
  · have hsR : Construction.typeTwoSpine p ∈ p.val ∩ (c.remainingEdges \ c.old) :=
      mem_inter.mpr ⟨(mem_inter.mp hs).1,
        mem_sdiff.mpr ⟨c.newEdges_subset_remaining (mem_inter.mp hs).2,
          (mem_sdiff.mp (mem_inter.mp hs).2).2⟩⟩
    exact (mem_inter.mp (hred.symm ▸ hsR)).1

include hQ in
private theorem exists_book (p : {T // T ∈ c.typeTwo}) :
    ∃ b : Book V, b.pages = pages c Q p ∧ b.spine = Construction.typeTwoSpine p :=
  Book.exists_representation (pages c Q p) (Construction.typeTwoSpine p)
    (Layered.pages_nonempty _ _ _ p) ((pages_card_le_two c hQ p).trans (by decide))
    (fun _ hT => (mem_trianglesOn.mp
      (typeFamily_subset _ _ _ (pages_subset c hQ p hT))).1)
    (pages_common_spine c p)

noncomputable def book (p : {T // T ∈ c.typeTwo}) : Book V :=
  Classical.choose (exists_book c hQ p)

theorem book_pages (p : {T // T ∈ c.typeTwo}) :
    (book c hQ p).pages = pages c Q p :=
  (Classical.choose_spec (exists_book c hQ p)).1

theorem book_spine (p : {T // T ∈ c.typeTwo}) :
    (book c hQ p).spine = Construction.typeTwoSpine p :=
  (Classical.choose_spec (exists_book c hQ p)).2

theorem book_spine_mem (p : {T // T ∈ c.typeTwo}) :
    (book c hQ p).spine ∈ c.newEdges := by
  rw [book_spine]
  exact (mem_inter.mp (Construction.typeTwoSpine_mem p)).2

theorem book_parent_mem (p : {T // T ∈ c.typeTwo}) : p.val ∈ (book c hQ p).pages := by
  rw [book_pages]
  exact Layered.mem_twoLayerPages.mpr (Or.inl rfl)

theorem books_disjoint : Books.DisjointSupports (fun p => (book c hQ p).pages) := by
  simpa only [book_pages, pages] using
    Layered.supports_disjoint (typeTwo_colored c.remainingEdges c.old)
      c.typeTwo_maximum (residual_packing c hQ)

theorem books_everyChoiceMeets :
    Books.EveryChoiceMeets (typeFamily c.remainingEdges c.old 2)
      (fun p => (book c hQ p).pages) := by
  simp only [book_pages, pages]
  exact Books.everyChoiceMeets_of_maximum
    (fun _ hT => trianglesOn_nonempty (typeFamily_subset _ _ _ hT))
    (fun _ hf => Layered.choices_maximum (typeTwo_colored c.remainingEdges c.old)
      c.typeTwo_maximum (residual_packing c hQ) hf)

theorem book_blue_old (p : {T // T ∈ c.typeTwo})
    {U : Finset (Sym2 V)} (hU : U ∈ (book c hQ p).pages) :
    U \ {(book c hQ p).spine} ⊆ c.oldRemaining := by
  rw [book_pages] at hU
  have hactual := typeFamily_subset _ _ _ (pages_subset c hQ p hU)
  have hs := pages_common_spine c p U hU
  have hsN := (mem_inter.mp (Construction.typeTwoSpine_mem p)).2
  intro e he
  obtain ⟨heU, heSpine⟩ := mem_sdiff.mp he
  have heRemain := (mem_trianglesOn.mp hactual).2 heU
  have heOld : e ∈ c.old := by
    by_contra hn
    have heq := card_le_one.mp (c.remaining_new_le_one hactual)
      e (mem_sdiff.mpr ⟨heU, hn⟩) (Construction.typeTwoSpine p)
      (mem_sdiff.mpr ⟨hs, (mem_sdiff.mp hsN).2⟩)
    exact heSpine (mem_singleton.mpr (heq.trans (book_spine c hQ p).symm))
  exact mem_sdiff.mpr ⟨heOld, (mem_sdiff.mp heRemain).2⟩

/-- The old edges in the one-page books form the fixed part of the cover. -/
noncomputable def fixedOld (Q : Finset (Finset (Sym2 V))) : Finset (Sym2 V) :=
  blueEdges (c.remainingEdges \ c.old)
    (c.typeTwo \ Layered.pairedParents (c.remainingEdges \ c.old) c.typeTwo Q)

include hQ in
theorem fixedOld_card : (fixedOld c Q).card + 2 * Q.card = 2 * c.typeTwo.card := by
  classical
  let R := c.remainingEdges \ c.old
  let P := Layered.pairedParents R c.typeTwo Q
  have hpaired : P.card = Q.card :=
    Layered.pairedParents_card (typeTwo_colored c.remainingEdges c.old)
      c.typeTwo_maximum (residual_packing c hQ)
  have hsub : P ⊆ c.typeTwo := Layered.pairedParents_subset R c.typeTwo Q
  have hblue : (fixedOld c Q).card = 2 * (c.typeTwo \ P).card :=
    (c.typeTwo_maximum.1.subfamily sdiff_subset).card_blueEdges
      (typeTwo_colored c.remainingEdges c.old)
  have hsplit := card_sdiff_add_card_eq_card hsub
  omega

theorem fixedOld_subset : fixedOld c Q ⊆ c.oldRemaining := by
  intro e he
  obtain ⟨heP, heR⟩ := mem_blueEdges.mp he
  obtain ⟨p, hp, hep⟩ := mem_support.mp heP
  have hpB := (mem_sdiff.mp hp).1
  have heRemain := c.rest_support_subset
    (mem_support.mpr ⟨p, c.typeTwo_subset_rest hpB, hep⟩)
  have heOld : e ∈ c.old := by
    by_contra hn
    exact heR (mem_sdiff.mpr ⟨heRemain, hn⟩)
  exact mem_sdiff.mpr ⟨heOld, (mem_sdiff.mp heRemain).2⟩

theorem book_single_fixedOld (p : {T // T ∈ c.typeTwo})
    (hc : (book c hQ p).pages.card = 1) :
    ∀ U ∈ (book c hQ p).pages, U ∩ c.oldRemaining ⊆ fixedOld c Q := by
  have hnot : p.val ∉ Layered.pairedParents
      (c.remainingEdges \ c.old) c.typeTwo Q := by
    intro hp
    have htwo := Layered.pages_card_paired (typeTwo_colored c.remainingEdges c.old)
      (residual_packing c hQ) p hp
    rw [book_pages] at hc
    change (pages c Q p).card = 2 at htwo
    omega
  intro U hU e he
  have hUp := card_le_one.mp (show (book c hQ p).pages.card ≤ 1 by omega)
    U hU p.val (book_parent_mem c hQ p)
  obtain ⟨heU, heOld⟩ := mem_inter.mp he
  apply mem_blueEdges.mpr
  refine ⟨mem_support.mpr ⟨p.val, mem_sdiff.mpr ⟨p.property, hnot⟩, hUp ▸ heU⟩, ?_⟩
  intro heR
  exact (mem_sdiff.mp heR).2 (mem_sdiff.mp heOld).1

theorem book_child_of_opposite (p : {T // T ∈ c.typeTwo}) {e : Sym2 V}
    (hop : (book c hQ p).opposite = some e) :
    ∃ q ∈ Q, q ∈ (book c hQ p).pages := by
  have hpaired : p.val ∈ Layered.pairedParents
      (c.remainingEdges \ c.old) c.typeTwo Q := by
    by_contra hn
    have hone := Layered.pages_card_unpaired p hn
    have htwo := Book.pages_card_of_opposite hop
    rw [book_pages] at htwo
    change (pages c Q p).card = 1 at hone
    omega
  obtain ⟨_, q, hq, hred⟩ := Layered.mem_pairedParents.mp hpaired
  refine ⟨q, hq, ?_⟩
  rw [book_pages]
  exact Layered.mem_twoLayerPages.mpr (Or.inr ⟨hq, hred.symm⟩)

theorem oppositeBooks_card_le_privateRed :
    (oppositeBooks c.remainingEdges c.oldRemaining c.newEdges (book c hQ)).card ≤
      (privateRedPages c.specialFamily c.newEdges Q).card := by
  apply OppositeEdges.random_books_card_le_privateRed c hQ (book c hQ)
    (fun p => ⟨p.val, p.property, book_parent_mem c hQ p⟩)
    (book_spine_mem c hQ) ?_ (books_disjoint c hQ)
  intro p hp
  obtain ⟨e, hop, _, _⟩ := mem_oppositeBooks.mp hp
  exact book_child_of_opposite c hQ p hop

include hQ in
/-- The random-cover estimate for G' using the second-page packing Q. -/
theorem remaining_random_cover :
    8 * transversalNumber (trianglesOn c.remainingEdges) + 8 * Q.card
      ≤ 4 * c.oldRemaining.card + 12 * c.typeTwo.card
        + 3 * (privateRedPages c.specialFamily c.newEdges Q).card := by
  have hNO : Disjoint c.newEdges c.oldRemaining :=
    c.newEdges_disjoint_old.mono_right sdiff_subset
  have hchoice : Books.EveryChoiceMeets
      (typeFamily c.remainingEdges c.oldRemaining 2) (fun p => (book c hQ p).pages) := by
    rw [c.typeFamily_oldRemaining]
    exact books_everyChoiceMeets c hQ
  have hcut := random_book_cover (book c hQ)
    (fun _ hT => c.remaining_oldRemaining_ge_two hT) hNO (fixedOld_subset c)
    (fun _ he => c.old_not_diag (mem_sdiff.mp he).1)
    (fun _ he => c.newEdges_not_diag he) (book_spine_mem c hQ)
    (fun p _ hU => book_blue_old c hQ p hU) (book_single_fixedOld c hQ) hchoice
  have hW := fixedOld_card c hQ
  have hN := c.card_newEdges
  have hprivate := oppositeBooks_card_le_privateRed c hQ
  omega

include hQ in
/-- Restoring the first packing gives the random-cover inequality in G. -/
theorem random_cover :
    8 * transversalNumber (trianglesOn edges) + 8 * Q.card
      ≤ 12 * c.initial.card + 20 * c.first.card + 12 * c.typeTwo.card
        + 3 * (privateRedPages c.specialFamily c.newEdges Q).card := by
  have hdelete := transversalNumber_le_add_residual
    (trianglesOn edges) (support c.first) (fun _ hT => trianglesOn_nonempty hT)
  rw [← trianglesOn_sdiff] at hdelete
  have hfirst : (support c.first).card = 3 * c.first.card :=
    c.first_packing.card_support_uniform (fun _ hT => trianglesOn_card (c.first_packing.1 hT))
  have hremaining := remaining_random_cover c hQ
  have hOld := c.oldRemaining_card
  change transversalNumber (trianglesOn edges) ≤
    (support c.first).card + transversalNumber (trianglesOn c.remainingEdges) at hdelete
  omega

end TwoLayer
end Tuza
