import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
Finite families of edge sets. These definitions are independent of graph geometry.
Graph triangles are connected to them in the graph module.
-/

namespace Tuza

open Finset

variable {E : Type*} [DecidableEq E]

/-- The union of the edges used by a family. -/
def support (P : Finset (Finset E)) : Finset E := P.biUnion id

@[simp] theorem mem_support {e : E} {P : Finset (Finset E)} :
    e ∈ support P ↔ ∃ T ∈ P, e ∈ T := by
  simp [support]

@[simp] theorem support_insert (T : Finset E) (P : Finset (Finset E)) :
    support (insert T P) = T ∪ support P := by
  simp [support]

theorem support_mono {P Q : Finset (Finset E)} (h : P ⊆ Q) :
    support P ⊆ support Q := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact mem_support.mpr ⟨T, h hT, heT⟩

/-- A packing consists of members of the family that are pairwise edge-disjoint. -/
def IsPacking (F P : Finset (Finset E)) : Prop :=
  P ⊆ F ∧ (P : Set (Finset E)).Pairwise Disjoint

/-- Maximum is with respect to the number of triangles. -/
def IsMaximumPacking (F P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q → Q.card ≤ P.card

/-- A transversal meets every member in an edge. -/
def IsCover (F : Finset (Finset E)) (C : Finset E) : Prop :=
  ∀ T ∈ F, (T ∩ C).Nonempty

/-- Deleting selected edges removes every member that meets one of them. -/
def residual (F : Finset (Finset E)) (C : Finset E) : Finset (Finset E) :=
  F.filter (fun T => Disjoint T C)

@[simp] theorem mem_residual {F : Finset (Finset E)} {C T : Finset E} :
    T ∈ residual F C ↔ T ∈ F ∧ Disjoint T C := by
  simp [residual]

omit [DecidableEq E] in
theorem packing_empty (F : Finset (Finset E)) : IsPacking F ∅ := by
  simp [IsPacking, Set.Pairwise]

omit [DecidableEq E] in
theorem IsPacking.subfamily {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : Q ⊆ P) : IsPacking F Q := by
  exact ⟨hQ.trans hP.1, fun T hT U hU hne => hP.2 (hQ hT) (hQ hU) hne⟩

omit [DecidableEq E] in
theorem IsPacking.mono_family {F F' P : Finset (Finset E)}
    (hP : IsPacking F P) (hF : F ⊆ F') : IsPacking F' P :=
  ⟨hP.1.trans hF, hP.2⟩

theorem IsPacking.union {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : IsPacking F Q)
    (hd : Disjoint (support P) (support Q)) : IsPacking F (P ∪ Q) := by
  refine ⟨union_subset hP.1 hQ.1, ?_⟩
  have hcross : ∀ T ∈ P, ∀ U ∈ Q, Disjoint T U := by
    intro T hT U hU
    exact hd.mono (fun e he => mem_support.mpr ⟨T, hT, he⟩)
      (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  intro T hT U hU hne
  rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
  · exact hP.2 hT hU hne
  · exact hcross T hT U hU
  · exact (hcross U hU T hT).symm
  · exact hQ.2 hT hU hne

theorem disjoint_of_support_disjoint {P Q : Finset (Finset E)}
    (hne : ∀ T ∈ P, T.Nonempty) (hd : Disjoint (support P) (support Q)) :
    Disjoint P Q := by
  apply disjoint_left.mpr
  intro T hT hU
  obtain ⟨e, he⟩ := hne T hT
  exact disjoint_left.mp hd (mem_support.mpr ⟨T, hT, he⟩)
    (mem_support.mpr ⟨T, hU, he⟩)

omit [DecidableEq E] in
theorem exists_maximumPacking (F : Finset (Finset E)) :
    ∃ P, IsMaximumPacking F P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P, hP, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hc⟩
  refine ⟨P, (mem_filter.mp hP).2, ?_⟩
  intro Q hQ
  exact hmax Q (mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩)

/-- One maximum packing, chosen from the finite collection of all packings. -/
noncomputable def maximumPacking (F : Finset (Finset E)) : Finset (Finset E) :=
  Classical.choose (exists_maximumPacking F)

omit [DecidableEq E] in
theorem maximumPacking_spec (F : Finset (Finset E)) :
    IsMaximumPacking F (maximumPacking F) :=
  Classical.choose_spec (exists_maximumPacking F)

/-- The maximum packing size. -/
noncomputable def packingNumber (F : Finset (Finset E)) : ℕ :=
  (maximumPacking F).card

omit [DecidableEq E] in
theorem IsPacking.card_le {F P : Finset (Finset E)} (hP : IsPacking F P) :
    P.card ≤ packingNumber F :=
  (maximumPacking_spec F).2 P hP

omit [DecidableEq E] in
theorem IsMaximumPacking.card_eq {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) : P.card = packingNumber F := by
  apply Nat.le_antisymm hP.1.card_le
  exact hP.2 _ (maximumPacking_spec F).1

omit [DecidableEq E] in
theorem IsPacking.maximum_of_card_eq {F P : Finset (Finset E)}
    (hP : IsPacking F P) (hc : P.card = packingNumber F) :
    IsMaximumPacking F P := by
  refine ⟨hP, fun Q hQ => ?_⟩
  rw [hc]
  exact hQ.card_le

theorem packing_insert {F P : Finset (Finset E)} {T : Finset E}
    (hP : IsPacking F P) (hT : T ∈ F) (hd : Disjoint T (support P)) :
    IsPacking F (insert T P) := by
  refine ⟨insert_subset hT hP.1, ?_⟩
  intro U hU V hV hne
  have hdis : ∀ U ∈ P, Disjoint T U := by
    intro U hU
    exact hd.mono_right (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  simp only [mem_coe, mem_insert] at hU hV
  rcases hU with rfl | hU
  · rcases hV with rfl | hV
    · exact False.elim (hne rfl)
    · exact hdis V hV
  · rcases hV with rfl | hV
    · exact (hdis U hU).symm
    · exact hP.2 hU hV hne

theorem IsMaximumPacking.meets_support {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {T : Finset E} (hT : T ∈ F)
    (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hlt := hP.2 (insert T P) (packing_insert hP.1 hT hd)
  simp [hnot] at hlt

theorem IsMaximumPacking.support_covers {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

theorem IsPacking.disjoint_support_erase {F P : Finset (Finset E)}
    (hP : IsPacking F P) {S T : Finset E} (hS : S ∈ P)
    (hT : ∀ e ∈ T, e ∈ support P → e ∈ S) :
    Disjoint T (support (P.erase S)) := by
  apply disjoint_left.mpr
  intro e heT heP
  obtain ⟨U, hU, heU⟩ := mem_support.mp heP
  obtain ⟨hUS, hUP⟩ := mem_erase.mp hU
  have heS := hT e heT (mem_support.mpr ⟨U, hUP, heU⟩)
  exact disjoint_left.mp (hP.2 hUP hS hUS) heU heS

/-- Replacing one member of a maximum packing by two disjoint members is impossible. -/
theorem IsMaximumPacking.no_two_for_one {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {S T U : Finset E}
    (hS : S ∈ P) (hT : T ∈ F) (hU : U ∈ F)
    (hneT : T.Nonempty) (hneU : U.Nonempty) (hdTU : Disjoint T U)
    (hdT : Disjoint T (support (P.erase S)))
    (hdU : Disjoint U (support (P.erase S))) : False := by
  have hbase := hP.1.subfamily (erase_subset S P)
  have hfirst := packing_insert hbase hT hdT
  have hsecond : IsPacking F (insert U (insert T (P.erase S))) := by
    apply packing_insert hfirst hU
    rw [support_insert]
    exact disjoint_union_right.mpr ⟨hdTU.symm, hdU⟩
  have ht : T ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneT
    exact disjoint_left.mp hdT he (mem_support.mpr ⟨T, hmem, he⟩)
  have hu : U ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdU he (mem_support.mpr ⟨U, hmem, he⟩)
  have hUT : U ≠ T := by
    rintro rfl
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdTU he he
  have hbound := hP.2 _ hsecond
  have hsize := card_erase_add_one hS
  simp only [card_insert_of_notMem ht,
    card_insert_of_notMem (by simp [hu, hUT] : U ∉ insert T (P.erase S))] at hbound
  omega

theorem support_covers (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) : IsCover F (support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hF T hT
  exact ⟨e, mem_inter.mpr ⟨he, mem_support.mpr ⟨T, hT, he⟩⟩⟩

/-- Minimum transversal size; the theorems below ensure attainment for
families of nonempty edge sets, in particular for triangle families. -/
noncomputable def transversalNumber (F : Finset (Finset E)) : ℕ :=
  sInf {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}

theorem IsCover.number_le {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : transversalNumber F ≤ C.card := by
  exact csInf_le (OrderBot.bddBelow _) ⟨C, hC, rfl⟩

theorem exists_minimumCover (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, IsCover F C ∧ C.card = transversalNumber F := by
  have hex : {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}.Nonempty :=
    ⟨(support F).card, support F, support_covers F hF, rfl⟩
  exact csInf_mem hex

theorem IsCover.mono {F : Finset (Finset E)} {C D : Finset E}
    (hC : IsCover F C) (hCD : C ⊆ D) : IsCover F D := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1, hCD (mem_inter.mp he).2⟩⟩

theorem IsCover.mono_family {F F' : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) (hF : F' ⊆ F) : IsCover F' C :=
  fun T hT => hC T (hF hT)

/-- Extraneous edges never help a transversal: every cover can be restricted
to the edges that actually occur in the family. -/
theorem IsCover.inter_support {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : IsCover F (C ∩ support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  obtain ⟨heT, heC⟩ := mem_inter.mp he
  exact ⟨e, mem_inter.mpr ⟨heT,
    mem_inter.mpr ⟨heC, mem_support.mpr ⟨T, hT, heT⟩⟩⟩⟩

theorem exists_minimumCover_subset_support (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, C ⊆ support F ∧ IsCover F C ∧ C.card = transversalNumber F := by
  obtain ⟨C, hC, hc⟩ := exists_minimumCover F hF
  refine ⟨C ∩ support F, inter_subset_right, hC.inter_support, ?_⟩
  exact Nat.le_antisymm ((card_le_card inter_subset_left).trans_eq hc)
    hC.inter_support.number_le

theorem cover_union_residual {F : Finset (Finset E)} {C D : Finset E}
    (hD : IsCover (residual F C) D) : IsCover F (C ∪ D) := by
  intro T hT
  by_cases hd : Disjoint T C
  · obtain ⟨e, he⟩ := hD T (mem_residual.mpr ⟨hT, hd⟩)
    exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1,
      mem_union_right _ (mem_inter.mp he).2⟩⟩
  · obtain ⟨e, heT, heC⟩ := not_disjoint_iff.mp hd
    exact ⟨e, mem_inter.mpr ⟨heT, mem_union_left _ heC⟩⟩

theorem transversalNumber_le_add_residual (F : Finset (Finset E)) (C : Finset E)
    (hF : ∀ T ∈ F, T.Nonempty) :
    transversalNumber F ≤ C.card + transversalNumber (residual F C) := by
  obtain ⟨D, hD, hcard⟩ := exists_minimumCover (residual F C)
    (fun T hT => hF T (mem_residual.mp hT).1)
  calc
    transversalNumber F ≤ (C ∪ D).card := (cover_union_residual hD).number_le
    _ ≤ C.card + D.card := card_union_le C D
    _ = _ := by rw [hcard]

theorem IsPacking.card_support {F P : Finset (Finset E)} (hP : IsPacking F P) :
    (support P).card = ∑ T ∈ P, T.card := by
  exact card_biUnion hP.2

theorem IsPacking.card_support_uniform {F P : Finset (Finset E)}
    (hP : IsPacking F P) {k : ℕ} (hcard : ∀ T ∈ P, T.card = k) :
    (support P).card = k * P.card := by
  rw [hP.card_support]
  calc
    ∑ T ∈ P, T.card = ∑ _T ∈ P, k := sum_congr rfl hcard
    _ = k * P.card := by simp [Nat.mul_comm]

theorem transversalNumber_le_three_packingNumber (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.card = 3) :
    transversalNumber F ≤ 3 * packingNumber F := by
  have hne : ∀ T ∈ F, T.Nonempty := by
    intro T hT
    exact card_pos.mp (by rw [hF T hT]; decide)
  have hP := maximumPacking_spec F
  calc
    transversalNumber F ≤ (support (maximumPacking F)).card :=
      (hP.support_covers hne).number_le
    _ = 3 * packingNumber F :=
      hP.1.card_support_uniform (fun T hT => hF T (hP.1.1 hT))

/-- First maximize the number of members in S, then the total packing size. -/
def IsLexMaximumPacking (F S P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q →
    (Q ∩ S).card ≤ (P ∩ S).card ∧
    ((Q ∩ S).card = (P ∩ S).card → Q.card ≤ P.card)

theorem exists_lexMaximumPacking (F S : Finset (Finset E)) :
    ∃ P, IsLexMaximumPacking F S P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P₀, hP₀, hmax₀⟩ := candidates.exists_max_image
    (fun P => (P ∩ S).card) ⟨∅, hc⟩
  let tied := candidates.filter (fun P => (P ∩ S).card = (P₀ ∩ S).card)
  have htied : P₀ ∈ tied := by simp [tied, hP₀]
  obtain ⟨P, hP, hmax⟩ := tied.exists_max_image Finset.card ⟨P₀, htied⟩
  obtain ⟨hPc, hPeq⟩ := mem_filter.mp hP
  refine ⟨P, (mem_filter.mp hPc).2, ?_⟩
  intro Q hQ
  have hQc : Q ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    exact hmax₀ Q hQc
  · intro hQeq
    exact hmax Q (mem_filter.mpr ⟨hQc, hQeq.trans hPeq⟩)

theorem IsLexMaximumPacking.typePart_maximum {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hSF : S ⊆ F) :
    IsMaximumPacking S (P ∩ S) := by
  have hp : IsPacking S (P ∩ S) :=
    ⟨inter_subset_right, fun T hT U hU hne =>
      hP.1.2 (mem_inter.mp hT).1 (mem_inter.mp hU).1 hne⟩
  refine ⟨hp, fun Q hQ => ?_⟩
  have hbound := (hP.2 Q (hQ.mono_family hSF)).1
  simpa [inter_eq_left.mpr hQ.1] using hbound

theorem IsLexMaximumPacking.meets_support {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) {T : Finset E}
    (hT : T ∈ F) (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hins := packing_insert hP.1 hT hd
  have hlex := hP.2 (insert T P) hins
  have hmono : (P ∩ S).card ≤ (insert T P ∩ S).card :=
    card_le_card (inter_subset_inter (subset_insert T P) Subset.rfl)
  have heq := Nat.le_antisymm hlex.1 hmono
  have hcard := hlex.2 heq
  simp [hnot] at hcard

theorem IsLexMaximumPacking.support_covers {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

/-- Any packing with the same two optimal counts retains the same maximality. -/
theorem IsLexMaximumPacking.of_same_counts {F S P Q : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hQ : IsPacking F Q)
    (hfirst : (Q ∩ S).card = (P ∩ S).card) (hsecond : Q.card = P.card) :
    IsLexMaximumPacking F S Q := by
  refine ⟨hQ, fun U hU => ?_⟩
  obtain ⟨hu₁, hu₂⟩ := hP.2 U hU
  rw [hfirst, hsecond]
  exact ⟨hu₁, hu₂⟩

end Tuza
