import Tuza.Colored.Exchange
import Tuza.Books.Layered
import Tuza.Basic.Arithmetic
import Tuza.Basic.Coloring

/-! The two colored covering bounds: Lemma 2.3. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem paired_geometry {A R : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (q : {T // T ∈ Q}) :
    ∃ u v x y,
      (Layered.parent (oneRedTriangles_colored A R) hP hQ q).val = triangleEdges u v x ∧
      q.val = triangleEdges u v y ∧ s(u, v) ∈ R ∧ [u, v, x, y].Nodup := by
  classical
  let hF := oneRedTriangles_colored A R
  let p := Layered.parent hF hP hQ q
  have hpF := hP.1.1 p.property
  have hqF := (mem_residual.mp (hQ.1 q.property)).1
  have hn : (p.val ∩ R).Nonempty := card_pos.mp (by rw [(hF p.val hpF).2]; decide)
  obtain ⟨e, he⟩ := hn
  obtain ⟨⟨u, v⟩, rfl⟩ := Sym2.mk_surjective e
  have heq : s(u, v) ∈ q.val ∩ R := Layered.parent_spec hF hP hQ q ▸ he
  have hpReal := (mem_oneRedTriangles.mp hpF).1
  have hqReal := (mem_oneRedTriangles.mp hqF).1
  have huv := hpReal.ne_of_mem (mem_inter.mp he).1
  obtain ⟨x, hux, hvx, hpx⟩ := hpReal.exists_third_of_mem (mem_inter.mp he).1
  obtain ⟨y, huy, hvy, hqy⟩ := hqReal.exists_third_of_mem (mem_inter.mp heq).1
  have hxy : x ≠ y := by
    intro h
    have hpq : p.val = q.val := by rw [hpx, hqy, h]
    exact Layered.residual_member_not_parent hF hQ q.property (hpq ▸ p.property)
  refine ⟨u, v, x, y, hpx, hqy, (mem_inter.mp he).2, ?_⟩
  simp [List.nodup_cons, huv, hux, huy, hvx, hvy, hxy]

/-- A fixed opposite edge handles every triangle that misses the chosen red spines.
If it is needed, the associated residual page has a private red edge. -/
private theorem paired_extra {A R : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (q : {T // T ∈ Q}) :
    ∃ e : Sym2 V, ∀ T ∈ oneRedTriangles A R,
      ¬ Disjoint T (Layered.parent (oneRedTriangles_colored A R) hP hQ q).val →
      ¬ Disjoint T q.val → Disjoint T (redEdges R P) →
      e ∈ T ∧ ∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q.val ∩ R → W = q.val := by
  classical
  let hF := oneRedTriangles_colored A R
  let p := Layered.parent hF hP hQ q
  obtain ⟨u, v, x, y, hp, hq, hred, hvertices⟩ := paired_geometry hP hQ q
  refine ⟨s(x, y), ?_⟩
  intro T hT hTp hTq hdR
  have hparent : triangleEdges u v x ∈ P := hp ▸ p.property
  have hpage : triangleEdges u v y ∈
      residual (oneRedTriangles A R) (blueEdges R P) := hq ▸ hQ.1 q.property
  have hspineP : s(u, v) ∈ redEdges R P :=
    mem_redEdges.mpr ⟨mem_support.mpr ⟨triangleEdges u v x, hparent, by simp⟩, hred⟩
  have havoid : s(u, v) ∉ T := fun h => disjoint_left.mp hdR h hspineP
  obtain ⟨ep, hep, hepp⟩ := not_disjoint_iff.mp hTp
  obtain ⟨eq, heq, heqq⟩ := not_disjoint_iff.mp hTq
  have hx : (T ∩ triangleEdges u v x).Nonempty :=
    ⟨ep, mem_inter.mpr ⟨hep, hp ▸ hepp⟩⟩
  have hy : (T ∩ triangleEdges u v y).Nonempty :=
    ⟨eq, mem_inter.mpr ⟨heq, hq ▸ heqq⟩⟩
  have hreal := (mem_oneRedTriangles.mp hT).1
  have hopp := two_page_opposite_mem hreal hvertices havoid hx hy
  have hoppA := (mem_oneRedTriangles.mp hT).2.1 hopp
  have hoppNew : s(x, y) ∉ redEdges R P := fun h => disjoint_left.mp hdR hopp h
  have hoppR : s(x, y) ∈ R := by
    obtain ⟨f, hf⟩ := card_pos.mp (by rw [(hF T hT).2]; decide)
    obtain ⟨hfT, hfR⟩ := mem_inter.mp hf
    have hparentRed : ∀ e ∈ triangleEdges u v x, e ∈ R → e ∈ redEdges R P := by
      intro e he heR
      exact mem_redEdges.mpr ⟨mem_support.mpr ⟨_, hparent, he⟩, heR⟩
    have hchildRed : ∀ e ∈ triangleEdges u v y, e ∈ R → e ∈ redEdges R P := by
      intro e he heR
      exact residual_red_subset_parent_red hF hP hpage (mem_inter.mpr ⟨he, heR⟩)
    rcases two_page_triangle hreal hvertices havoid hx hy with h | h <;>
      rw [h] at hfT <;> rcases mem_triangleEdges.mp hfT with rfl | rfl | rfl
    · exact (disjoint_left.mp hdR (by simp [h])
        (hparentRed _ (by simp) hfR)).elim
    · exact (disjoint_left.mp hdR (by simp [h])
        (hchildRed _ (by simp) hfR)).elim
    · exact hfR
    · exact (disjoint_left.mp hdR (by simp [h])
        (hparentRed _ (by simp) hfR)).elim
    · exact (disjoint_left.mp hdR (by simp [h])
        (hchildRed _ (by simp) hfR)).elim
    · exact hfR
  refine ⟨hopp, ?_⟩
  intro W hW hWR
  have huvQ : s(u, v) ∈ q.val ∩ R := mem_inter.mpr ⟨by simp [hq], hred⟩
  have huvW : s(u, v) ∈ W := (mem_inter.mp (hWR.symm ▸ huvQ)).1
  exact (unique_residual_triangle hP hparent hpage hred hoppA hoppR hoppNew W hW huvW).trans hq.symm

private theorem exists_first_cover_base {A R : Finset (Sym2 V)}
    {P Q J : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hJQ : J ⊆ Q)
    (hJ : ∀ q ∈ Q,
      (∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q ∩ R → W = q) → q ∈ J) :
    ∃ C, IsCover (oneRedTriangles A R) C ∧
      support (P \ Layered.pairedParents R P Q) ⊆ C ∧ redEdges R P ⊆ C ∧
      C.card + 2 * Q.card ≤ 3 * P.card + J.card := by
  classical
  let hF := oneRedTriangles_colored A R
  choose opposite hopposite using
    (fun q : {T // T ∈ Q} => paired_extra hP hQ q)
  let W := P \ Layered.pairedParents R P Q
  let extras := J.attach.image (fun q => opposite ⟨q.val, hJQ q.property⟩)
  let base := blueEdges R W ∪ redEdges R P
  let C := base ∪ extras
  have hredC : redEdges R P ⊆ C := by
    intro e he
    exact mem_union_left _ (mem_union_right _ he)
  have hsingleC : support W ⊆ C := by
    intro e he
    apply mem_union_left
    by_cases hr : e ∈ R
    · exact mem_union_right _ (mem_redEdges.mpr
        ⟨support_mono sdiff_subset he, hr⟩)
    · exact mem_union_left _ (mem_blueEdges.mpr ⟨he, hr⟩)
  have hcover : IsCover (oneRedTriangles A R) C := by
    intro T hT
    by_contra hn
    have hd : Disjoint T C := disjoint_left.mpr (fun e heT heC =>
      hn ⟨e, mem_inter.mpr ⟨heT, heC⟩⟩)
    obtain ⟨p, hp⟩ := Books.exists_book_all_pages_meet_of_maximum
      (pages := Layered.twoLayerPages R P Q)
      (fun _ hS => hF.member_nonempty hS)
      (fun _ hf => Layered.choices_maximum hF hP hQ hf) hT
    have hTp := hp p.val (Layered.mem_twoLayerPages.mpr (Or.inl rfl))
    by_cases hpaired : p.val ∈ Layered.pairedParents R P Q
    · obtain ⟨_, q, hqQ, hpq⟩ := Layered.mem_pairedParents.mp hpaired
      have hchosen := Layered.parent_unique hF hP hQ ⟨q, hqQ⟩ p hpq
      have hTq := hp q (Layered.mem_twoLayerPages.mpr (Or.inr ⟨hqQ, hpq.symm⟩))
      have hTp' : ¬ Disjoint T (Layered.parent hF hP hQ ⟨q, hqQ⟩).val := by
        rw [← hchosen]
        exact hTp
      obtain ⟨heT, hprivate⟩ := hopposite ⟨q, hqQ⟩ T hT hTp' hTq (hd.mono_right hredC)
      have hqJ := hJ q hqQ hprivate
      have heExtra : opposite ⟨q, hqQ⟩ ∈ extras :=
        mem_image.mpr ⟨⟨q, hqJ⟩, mem_attach _ _, rfl⟩
      exact disjoint_left.mp hd heT (mem_union_right _ heExtra)
    · obtain ⟨e, heT, hep⟩ := not_disjoint_iff.mp hTp
      have heW : e ∈ support W :=
        mem_support.mpr ⟨p.val, mem_sdiff.mpr ⟨p.property, hpaired⟩, hep⟩
      exact disjoint_left.mp hd heT (hsingleC heW)
  have hWpacking := hP.1.subfamily (sdiff_subset : W ⊆ P)
  have hblue : (blueEdges R W).card = 2 * W.card := hWpacking.card_blueEdges hF
  have hred : (redEdges R P).card = P.card := hP.1.card_redEdges hF
  have hWcard : W.card + Q.card = P.card := by
    have h := card_sdiff_add_card_eq_card (Layered.pairedParents_subset R P Q)
    rw [Layered.pairedParents_card hF hP hQ] at h
    exact h
  have hextras : extras.card ≤ J.card := by
    calc
      extras.card ≤ J.attach.card := card_image_le
      _ = J.card := card_attach
  have hcard : C.card ≤ (blueEdges R W).card + (redEdges R P).card + J.card := by
    calc
      C.card ≤ base.card + extras.card := card_union_le _ _
      _ ≤ (blueEdges R W).card + (redEdges R P).card + J.card :=
        Nat.add_le_add (card_union_le _ _) hextras
  refine ⟨C, hcover, hsingleC, hredC, ?_⟩
  omega

/-- The first cover includes one opposite edge for each private residual page.
Every opposite edge that is actually needed is assigned to such a page by
`paired_extra`; counting additional private pages only enlarges the bound. -/
theorem exists_first_colored_cover {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    ∃ C, IsCover (oneRedTriangles A R) C ∧
      C.card + 2 * Q.card + U.card ≤ 3 * P.card +
        (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card := by
  classical
  let hF := oneRedTriangles_colored A R
  let J := privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q
  have hJQ : J ⊆ Q := privateRedPages_subset _ _ _
  have hJ : ∀ q ∈ Q,
      (∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q ∩ R → W = q) → q ∈ J := by
    intro q hq hp
    exact mem_privateRedPages.mpr ⟨hq, hp⟩
  obtain ⟨C, hC, hsingle, hred, hcard⟩ := exists_first_cover_base hP hQ hJQ hJ
  have hUP : U ⊆ P := hU.trans (privateRedPages_subset _ _ _)
  have hUunpaired : U ⊆ P \ Layered.pairedParents R P Q := by
    intro p hp
    obtain ⟨hpP, hprivate⟩ := mem_privateRedPages.mp (hU hp)
    refine mem_sdiff.mpr ⟨hpP, ?_⟩
    intro hpaired
    obtain ⟨_, q, hq, hpq⟩ := Layered.mem_pairedParents.mp hpaired
    have hqp := hprivate q (mem_residual.mp (hQ.1 hq)).1 hpq.symm
    exact Layered.residual_member_not_parent hF hQ hq (hqp.symm ▸ hpP)
  have hblueU : blueEdges R U ⊆ C :=
    (blueEdges_subset_support _ _).trans ((support_mono hUunpaired).trans hsingle)
  have hredU : redEdges R U ⊆ C := by
    intro e he
    obtain ⟨heU, heR⟩ := mem_redEdges.mp he
    exact hred (mem_redEdges.mpr ⟨support_mono hUP heU, heR⟩)
  have hremoved := hC.sdiff_privateRed hF hP.1 hU hblueU
  have hsize := card_sdiff_privateRed hF hP.1 hU hredU
  refine ⟨C \ redEdges R U, hremoved, ?_⟩
  change (C \ redEdges R U).card + 2 * Q.card + U.card ≤ 3 * P.card + J.card
  omega

theorem first_colored_cover {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    transversalNumber (oneRedTriangles A R) + 2 * Q.card + U.card ≤ 3 * P.card +
      (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card := by
  obtain ⟨C, hC, hc⟩ := exists_first_colored_cover hP hQ hU
  exact (Nat.add_le_add_right (Nat.add_le_add_right hC.number_le _) _).trans hc

/-- The first colored bound: equation (1). -/
theorem colored_bound {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsMaximumPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    3 * transversalNumber (oneRedTriangles A R) + 2 * U.card ≤ 8 * P.card := by
  have hfirst := first_colored_cover hP hQ.1 hU
  have hsecond := second_colored_cover (oneRedTriangles_colored A R) hP.1 hQ
  have hr := card_le_card
    (privateRedPages_subset (residual (oneRedTriangles A R) (blueEdges R P)) R Q)
  exact colored_bound_arithmetic hfirst hsecond hr

/-- Apply the first bound to the family left after deleting the parent blue edges. -/
theorem colored_refined {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsMaximumPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    4 * transversalNumber (oneRedTriangles A R) + U.card ≤
      9 * P.card + 6 * Q.card := by
  have hfirst := first_colored_cover hP hQ.1 hU
  have hQ' : IsMaximumPacking (oneRedTriangles (A \ blueEdges R P) R) Q := by
    rw [oneRedTriangles_sdiff]
    exact hQ
  have hlocal :
      3 * transversalNumber (residual (oneRedTriangles A R) (blueEdges R P)) +
        2 * (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card
      ≤ 8 * Q.card := by
    rw [← oneRedTriangles_sdiff A R (blueEdges R P)]
    exact colored_bound hQ' (maximumPacking_spec _) (Subset.refl _)
  have hdelete := transversalNumber_le_add_residual (oneRedTriangles A R) (blueEdges R P)
    (fun _ hT => (oneRedTriangles_colored A R).member_nonempty hT)
  have hblue : (blueEdges R P).card = 2 * P.card :=
    hP.1.card_blueEdges (oneRedTriangles_colored A R)
  have hresidual : 3 * transversalNumber (oneRedTriangles A R) +
      2 * (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card
      ≤ 6 * P.card + 8 * Q.card := by omega
  exact colored_refined_arithmetic hfirst hresidual

end Tuza
