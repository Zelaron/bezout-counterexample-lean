import BezoutCounterexample.Topology

/-!
# Compactness of sets of real points

A closed set of real points on which every function is bounded is compact
(`RealPt.isCompact_of_forall_bounded`); boundedness propagates through generators
(`RealPt.forall_bounded_of_gen`). Together, these are the compactness criterion of §2.1 of the
paper.
-/

noncomputable section


namespace BezoutCounterexample

open Set Topology

namespace RealPt

variable {U : Type*} [CommRing U]

lemma isClosed_range_coe : IsClosed (range fun w : RealPt U => (w : U → ℝ)) := by
  have : range (fun w : RealPt U => (w : U → ℝ)) =
      {f : U → ℝ | f 1 = 1} ∩ (⋂ x : U, ⋂ y : U, {f | f (x + y) = f x + f y}) ∩
        (⋂ x : U, ⋂ y : U, {f | f (x * y) = f x * f y}) := by
    ext f
    simp only [mem_range, mem_inter_iff, mem_setOf_eq, mem_iInter]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨⟨map_one w, fun x y => map_add w x y⟩, fun x y => map_mul w x y⟩
    · rintro ⟨⟨h1, hadd⟩, hmul⟩
      refine ⟨RealPt.ofHom
        { toFun := f, map_one' := h1, map_mul' := hmul,
          map_zero' := by have := hadd 0 0; simp at this; linarith,
          map_add' := hadd }, rfl⟩
  rw [this]
  refine ((isClosed_eq (continuous_apply 1) continuous_const).inter ?_).inter ?_
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x).add (continuous_apply y))
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x).mul (continuous_apply y))

lemma isClosedEmbedding_coe : IsClosedEmbedding (fun w : RealPt U => (w : U → ℝ)) :=
  ⟨⟨⟨rfl⟩, fun _ _ h => DFunLike.coe_injective h⟩, isClosed_range_coe⟩

/-- **Compactness criterion**: a closed set of real points on which every function is bounded is
compact. -/
theorem isCompact_of_forall_bounded {K' : Set (RealPt U)} (hK' : IsClosed K')
    (hb : ∀ x : U, ∃ C : ℝ, ∀ w ∈ K', |w x| ≤ C) : IsCompact K' := by
  choose C hC using hb
  have hbox : IsCompact (Set.pi univ fun x : U => Icc (-C x) (C x)) :=
    isCompact_univ_pi fun x => isCompact_Icc
  have hsub : (fun w : RealPt U => (w : U → ℝ)) '' K' ⊆ Set.pi univ fun x : U => Icc (-C x) (C x) := by
    rintro _ ⟨w, hw, rfl⟩ x -
    exact abs_le.1 (hC x w hw)
  have himg : IsCompact ((fun w : RealPt U => (w : U → ℝ)) '' K') :=
    hbox.of_isClosed_subset (isClosedEmbedding_coe.isClosedMap K' hK') hsub
  have := isClosedEmbedding_coe.isCompact_preimage himg
  rwa [Set.preimage_image_eq _ isClosedEmbedding_coe.injective] at this

/-- Boundedness propagates through generators. -/
theorem forall_bounded_of_gen {A : Type*} [CommRing A] [Algebra A U] {K : Set (RealPt A)}
    (hK : IsCompact K) {K' : Set (RealPt U)} (hmaps : ∀ w ∈ K', comap (algebraMap A U) w ∈ K)
    {s : Set U} (hgen : Algebra.adjoin A s = ⊤) (hs : ∀ y ∈ s, ∃ C : ℝ, ∀ w ∈ K', |w y| ≤ C)
    (x : U) : ∃ C : ℝ, ∀ w ∈ K', |w x| ≤ C := by
  have hx : x ∈ Algebra.adjoin A s := by rw [hgen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact hs y hy
  | algebraMap a =>
    obtain ⟨C, hC⟩ := (hK.image (continuous_eval a)).isBounded.exists_norm_le
    refine ⟨C, fun w hw => ?_⟩
    have := hC _ ⟨_, hmaps w hw, rfl⟩
    simpa [Real.norm_eq_abs] using this
  | add y z _ _ hy hz =>
    obtain ⟨C, hC⟩ := hy
    obtain ⟨D, hD⟩ := hz
    exact ⟨C + D, fun w hw => by
      rw [map_add]; exact (abs_add_le _ _).trans (add_le_add (hC w hw) (hD w hw))⟩
  | mul y z _ _ hy hz =>
    obtain ⟨C, hC⟩ := hy
    obtain ⟨D, hD⟩ := hz
    refine ⟨|C| * |D|, fun w hw => ?_⟩
    rw [map_mul, abs_mul]
    exact mul_le_mul ((hC w hw).trans (le_abs_self C)) ((hD w hw).trans (le_abs_self D))
      (abs_nonneg _) (abs_nonneg _)

end RealPt

end BezoutCounterexample

