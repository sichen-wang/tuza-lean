import Tuza.Basic.Coloring
import Tuza.Books.Families

/-!
Two-layer books obtained by pairing a maximum packing with a residual packing.
-/

namespace Tuza
namespace Layered

open Finset

variable {E : Type*} [DecidableEq E]

noncomputable def pairedParents (R : Finset E) (P Q : Finset (Finset E)) :
    Finset (Finset E) := by
  classical
  exact P.filter (fun p => ∃ q ∈ Q, p ∩ R = q ∩ R)

def children (R : Finset E) (Q : Finset (Finset E)) (p : Finset E) :
    Finset (Finset E) := Q.filter (fun q => q ∩ R = p ∩ R)

def twoLayerPages (R : Finset E) (P Q : Finset (Finset E))
    (p : {T // T ∈ P}) : Finset (Finset E) := insert p.val (children R Q p.val)

@[simp] theorem mem_pairedParents {R : Finset E} {P Q : Finset (Finset E)}
    {p : Finset E} :
    p ∈ pairedParents R P Q ↔ p ∈ P ∧ ∃ q ∈ Q, p ∩ R = q ∩ R := by
  classical
  simp [pairedParents]

@[simp] theorem mem_children {R : Finset E} {Q : Finset (Finset E)}
    {p q : Finset E} : q ∈ children R Q p ↔ q ∈ Q ∧ q ∩ R = p ∩ R := by
  simp [children]

@[simp] theorem mem_twoLayerPages {R : Finset E} {P Q : Finset (Finset E)}
    {p : {T // T ∈ P}} {T : Finset E} :
    T ∈ twoLayerPages R P Q p ↔ T = p.val ∨ (T ∈ Q ∧ T ∩ R = p.val ∩ R) := by
  simp [twoLayerPages]

theorem pairedParents_subset (R : Finset E) (P Q : Finset (Finset E)) :
    pairedParents R P Q ⊆ P := by
  intro p hp
  exact (mem_pairedParents.mp hp).1

variable {F P Q : Finset (Finset E)} {R : Finset E}

theorem exists_parent (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    ∃ p : {T // T ∈ P}, p.val ∩ R = q.val ∩ R := by
  have hq := hQ.1 q.property
  have hqF := (mem_residual.mp hq).1
  have hn : (q.val ∩ R).Nonempty := card_pos.mp (by rw [(hF q.val hqF).2]; decide)
  obtain ⟨e, he⟩ := hn
  have heP := residual_red_subset_parent_red hF hP hq he
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_redEdges.mp heP).1
  refine ⟨⟨p, hp⟩, ?_⟩
  have hpone := hF.red_eq_singleton (hP.1.1 hp) hep (mem_inter.mp he).2
  have hqone := hF.red_eq_singleton hqF (mem_inter.mp he).1 (mem_inter.mp he).2
  exact hpone.trans hqone.symm

noncomputable def parent (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    {T // T ∈ P} := Classical.choose (exists_parent hF hP hQ q)

theorem parent_spec (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    (parent hF hP hQ q).val ∩ R = q.val ∩ R :=
  Classical.choose_spec (exists_parent hF hP hQ q)

theorem parent_unique (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q})
    (p : {T // T ∈ P}) (heq : p.val ∩ R = q.val ∩ R) :
    p = parent hF hP hQ q := by
  apply Subtype.ext
  exact hP.1.red_inter_injective hF p.property (parent hF hP hQ q).property
    (heq.trans (parent_spec hF hP hQ q).symm)

theorem parent_injective (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Function.Injective (parent hF hP hQ) := by
  intro q₁ q₂ heq
  apply Subtype.ext
  apply hQ.red_inter_injective hF.residual q₁.property q₂.property
  calc
    q₁.val ∩ R = (parent hF hP hQ q₁).val ∩ R := (parent_spec hF hP hQ q₁).symm
    _ = (parent hF hP hQ q₂).val ∩ R := by rw [heq]
    _ = q₂.val ∩ R := parent_spec hF hP hQ q₂

theorem pairedParents_eq_image (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    pairedParents R P Q = Q.attach.image (fun q => (parent hF hP hQ q).val) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, q, hq, heq⟩ := mem_pairedParents.mp hp
    have hpq := parent_unique hF hP hQ ⟨q, hq⟩ ⟨p, hpP⟩ heq
    exact mem_image.mpr ⟨⟨q, hq⟩, mem_attach _ _, (congrArg Subtype.val hpq).symm⟩
  · intro hp
    obtain ⟨q, _, rfl⟩ := mem_image.mp hp
    exact mem_pairedParents.mpr ⟨(parent hF hP hQ q).property,
      q.val, q.property, parent_spec hF hP hQ q⟩

theorem pairedParents_card (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    (pairedParents R P Q).card = Q.card := by
  classical
  rw [pairedParents_eq_image hF hP hQ]
  have hinj : Function.Injective (fun q => (parent hF hP hQ q).val) := by
    intro q₁ q₂ heq
    exact parent_injective hF hP hQ (Subtype.ext heq)
  rw [card_image_of_injective _ hinj, card_attach]

theorem residual_packing_card_le (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) : Q.card ≤ P.card := by
  rw [← pairedParents_card hF hP hQ]
  exact card_le_card (pairedParents_subset R P Q)

/-- A residual page cannot be an original parent page: its two blue edges
avoid the parent support. -/
theorem residual_member_not_parent (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) {q : Finset E} (hq : q ∈ Q) :
    q ∉ P := by
  intro hqP
  have hqF := (mem_residual.mp (hQ.1 hq)).1
  have hn : (q \ R).Nonempty := card_pos.mp (by rw [hF.member_blue_card hqF]; decide)
  obtain ⟨e, he⟩ := hn
  obtain ⟨heq, heR⟩ := mem_sdiff.mp he
  exact disjoint_left.mp hQ.blueEdges_disjoint_parent_support
    (mem_blueEdges.mpr ⟨mem_support.mpr ⟨q, hq, heq⟩, heR⟩)
    (mem_support.mpr ⟨q, hqP, heq⟩)

theorem pages_nonempty (R : Finset E) (P Q : Finset (Finset E))
    (p : {T // T ∈ P}) : (twoLayerPages R P Q p).Nonempty := by
  exact ⟨p.val, mem_insert_self _ _⟩

theorem pages_subset_family (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    twoLayerPages R P Q p ⊆ F := by
  intro T hT
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, _⟩
  · exact hP.1.1 p.property
  · exact (mem_residual.mp (hQ.1 hTQ)).1

theorem pages_members_nonempty (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    (T : Finset E) (hT : T ∈ twoLayerPages R P Q p) : T.Nonempty :=
  hF.member_nonempty (pages_subset_family hP hQ p hT)

/-- All parent-support edges of a book belong to that book's parent. -/
theorem book_inter_parent_subset (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    support (twoLayerPages R P Q p) ∩ support P ⊆ p.val := by
  intro e he
  obtain ⟨hebook, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp hebook
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, hred⟩
  · exact heT
  · have heTR : e ∈ T ∩ R :=
      residual_inter_support_eq_inter_red hF hP (hQ.1 hTQ) ▸
        mem_inter.mpr ⟨heT, heP⟩
    exact (mem_inter.mp (hred ▸ heTR)).1

theorem supports_disjoint (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Books.DisjointSupports (twoLayerPages R P Q) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hdparents := hP.1.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, hTR⟩
  · have hep' := book_inter_parent_subset hF hP hQ p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hdparents heT hep'
  · rcases mem_twoLayerPages.mp hU with rfl | ⟨hUQ, hUR⟩
    · have hep := book_inter_parent_subset hF hP hQ p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hdparents hep heU
    · have hTU : T ≠ U := by
        intro heq
        apply hval
        apply hP.1.red_inter_injective hF p.property p'.property
        calc
          p.val ∩ R = T ∩ R := hTR.symm
          _ = U ∩ R := by rw [heq]
          _ = p'.val ∩ R := hUR
      exact disjoint_left.mp (hQ.2 hTQ hUQ hTU) heT heU

theorem choices_maximum (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q)
    {f : {T // T ∈ P} → Finset E}
    (hf : Books.ChoosesPages (twoLayerPages R P Q) f) :
    IsMaximumPacking F (Books.choice f) := by
  apply Books.choice_isMaximumPacking (pages_subset_family hP hQ)
    (supports_disjoint hF hP hQ) (pages_members_nonempty hF hP hQ) ?_ hf
  intro K hK
  simpa using hP.2 K hK

theorem children_card_le_one (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : Finset E) :
    (children R Q p).card ≤ 1 := by
  apply card_le_one.mpr
  intro T hT U hU
  obtain ⟨hTQ, hTR⟩ := mem_children.mp hT
  obtain ⟨hUQ, hUR⟩ := mem_children.mp hU
  exact hQ.red_inter_injective hF.residual hTQ hUQ (hTR.trans hUR.symm)

theorem children_nonempty_iff_paired (p : {T // T ∈ P}) :
    (children R Q p.val).Nonempty ↔ p.val ∈ pairedParents R P Q := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨hqQ, heq⟩ := mem_children.mp hq
    exact mem_pairedParents.mpr ⟨p.property, q, hqQ, heq.symm⟩
  · intro hp
    obtain ⟨_, q, hqQ, heq⟩ := mem_pairedParents.mp hp
    exact ⟨q, mem_children.mpr ⟨hqQ, heq.symm⟩⟩

theorem parent_not_child (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    p.val ∉ children R Q p.val := by
  intro hp
  exact residual_member_not_parent hF hQ (mem_children.mp hp).1 p.property

theorem pages_card_paired (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    (hp : p.val ∈ pairedParents R P Q) : (twoLayerPages R P Q p).card = 2 := by
  have hpos := card_pos.mpr ((children_nonempty_iff_paired p).mpr hp)
  have hle := children_card_le_one hF hQ p.val
  rw [twoLayerPages, card_insert_of_notMem (parent_not_child hF hQ p)]
  omega

theorem pages_eq_singleton_unpaired (p : {T // T ∈ P})
    (hp : p.val ∉ pairedParents R P Q) : twoLayerPages R P Q p = {p.val} := by
  have hempty : children R Q p.val = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    intro hn
    exact hp ((children_nonempty_iff_paired p).mp hn)
  simp [twoLayerPages, hempty]

theorem pages_card_unpaired (p : {T // T ∈ P})
    (hp : p.val ∉ pairedParents R P Q) : (twoLayerPages R P Q p).card = 1 := by
  rw [pages_eq_singleton_unpaired p hp, card_singleton]

theorem pages_eq_pair (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    {q : Finset E} (hq : q ∈ Q) (heq : q ∩ R = p.val ∩ R) :
    twoLayerPages R P Q p = {p.val, q} := by
  have hchild : children R Q p.val = {q} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTQ, hTR⟩ := mem_children.mp hT
      exact mem_singleton.mpr
        (hQ.red_inter_injective hF.residual hTQ hq (hTR.trans heq.symm))
    · intro hT
      have hTq := mem_singleton.mp hT
      subst T
      exact mem_children.mpr ⟨hq, heq⟩
  rw [twoLayerPages, hchild]

/-- If an actual red edge occurs only in its parent within the entire family,
that parent has no residual page. -/
theorem unique_red_parent_unpaired (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    {e : E} (hep : e ∈ p.val) (heR : e ∈ R)
    (hunique : ∀ T ∈ F, e ∈ T → T = p.val) : p.val ∉ pairedParents R P Q := by
  intro hp
  obtain ⟨_, q, hq, heq⟩ := mem_pairedParents.mp hp
  have heqR : e ∈ q ∩ R := heq ▸ mem_inter.mpr ⟨hep, heR⟩
  have hqp := hunique q (mem_residual.mp (hQ.1 hq)).1 (mem_inter.mp heqR).1
  exact residual_member_not_parent hF hQ hq (hqp ▸ p.property)

end Layered
end Tuza
