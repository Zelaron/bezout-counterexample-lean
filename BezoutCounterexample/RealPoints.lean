import BezoutCounterexample.Basic

/-!
# Section 2.1: real points and monotone surjections

* `RealPt A`: the real points `Spec(A)(ℝ)` of a ring `A`, i.e. the ring homomorphisms `A → ℝ`,
  with the coarsest topology for which every evaluation map `z ↦ z a` is continuous.
* `RealPt.comap f`: the continuous map `f^* : Spec(B)(ℝ) → Spec(A)(ℝ)`, `z ↦ z ∘ f`, induced by
  `f : A → B`.
* If `A = ℚ[a₁, …, a_m]`, then `z ↦ (z a₁, …, z a_m)` is a homeomorphism onto the real zero set
  in `ℝ^m` of the relations among the `aᵢ` (`RealPt.isEmbedding_evalGens`,
  `RealPt.range_evalGens`). In particular `Spec(A)(ℝ)` is Hausdorff, and a subset is compact if
  and only if it is closed and the generators are bounded on it (`RealPt.isCompact_iff`).
* `IsMonotoneSurjection q`: a continuous surjection `q : K' → K` all of whose fibres are connected
  (a *monotone* surjection); `IsMonotoneSurjOn q K' K`: `q` restricts to a monotone surjection
  `K' → K`.
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology

/-! ## Real points -/

/-- The real points `Spec(A)(ℝ)` of a commutative ring `A`: ring homomorphisms `A → ℝ`.
(For a `ℚ`-algebra these are automatically `ℚ`-algebra homomorphisms.) -/
def RealPt (A : Type*) [CommRing A] : Type _ := A →+* ℝ

namespace RealPt

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

instance : FunLike (RealPt A) A ℝ := inferInstanceAs (FunLike (A →+* ℝ) A ℝ)

instance : RingHomClass (RealPt A) A ℝ := inferInstanceAs (RingHomClass (A →+* ℝ) A ℝ)

/-- View a ring homomorphism `A → ℝ` as a real point. -/
def ofHom (φ : A →+* ℝ) : RealPt A := φ

/-- The ring homomorphism underlying a real point. -/
def toHom (z : RealPt A) : A →+* ℝ := z

@[simp] lemma ofHom_apply (φ : A →+* ℝ) (a : A) : ofHom φ a = φ a := rfl

@[simp] lemma toHom_apply (z : RealPt A) (a : A) : toHom z a = z a := rfl

@[ext] lemma ext {z w : RealPt A} (h : ∀ a, z a = w a) : z = w := DFunLike.ext _ _ h

/-- The topology on real points: the coarsest topology for which every evaluation `z ↦ z a` is
continuous. -/
instance : TopologicalSpace (RealPt A) :=
  TopologicalSpace.induced (fun z : RealPt A => (z : A → ℝ)) inferInstance

lemma continuous_eval (a : A) : Continuous fun z : RealPt A => z a :=
  (continuous_apply a).comp continuous_induced_dom

lemma continuous_iff {X : Type*} [TopologicalSpace X] {g : X → RealPt A} :
    Continuous g ↔ ∀ a, Continuous fun t => g t a := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- `Spec(A)(ℝ)` is Hausdorff. -/
instance : T2Space (RealPt A) :=
  (Topology.IsEmbedding.mk ⟨rfl⟩ (fun _ _ h => DFunLike.coe_injective h) :
    Topology.IsEmbedding fun z : RealPt A => (z : A → ℝ)).t2Space

/-- The map `f^* : Spec(B)(ℝ) → Spec(A)(ℝ)`, `z ↦ z ∘ f`, induced by `f : A → B`. -/
def comap (f : A →+* B) (z : RealPt B) : RealPt A := (toHom z).comp f

@[simp] lemma comap_apply (f : A →+* B) (z : RealPt B) (a : A) : comap f z a = z (f a) := rfl

/-- `f^*` is continuous. -/
lemma continuous_comap (f : A →+* B) : Continuous (comap f) :=
  continuous_iff.2 fun a => continuous_eval (f a)

lemma comap_comp (f : A →+* B) (g : B →+* C) (z : RealPt C) :
    comap (g.comp f) z = comap f (comap g z) := rfl

lemma isClosed_range_coe : IsClosed (range fun w : RealPt A => (w : A → ℝ)) := by
  have : range (fun w : RealPt A => (w : A → ℝ)) =
      {f : A → ℝ | f 1 = 1} ∩ (⋂ x : A, ⋂ y : A, {f | f (x + y) = f x + f y}) ∩
        (⋂ x : A, ⋂ y : A, {f | f (x * y) = f x * f y}) := by
    ext f
    simp only [mem_range, mem_inter_iff, mem_ofPred_eq, mem_iInter]
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

lemma isClosedEmbedding_coe : IsClosedEmbedding (fun w : RealPt A => (w : A → ℝ)) :=
  ⟨⟨⟨rfl⟩, fun _ _ h => DFunLike.coe_injective h⟩, isClosed_range_coe⟩

/-- A closed set of real points on which every function is bounded is compact. -/
theorem isCompact_of_forall_bounded {K' : Set (RealPt A)} (hK' : IsClosed K')
    (hb : ∀ x : A, ∃ C : ℝ, ∀ w ∈ K', |w x| ≤ C) : IsCompact K' := by
  choose C hC using hb
  have hbox : IsCompact (Set.pi univ fun x : A => Icc (-C x) (C x)) :=
    isCompact_univ_pi fun x => isCompact_Icc
  have hsub : (fun w : RealPt A => (w : A → ℝ)) '' K' ⊆
      Set.pi univ fun x : A => Icc (-C x) (C x) := by
    rintro _ ⟨w, hw, rfl⟩ x -
    exact abs_le.1 (hC x w hw)
  have himg : IsCompact ((fun w : RealPt A => (w : A → ℝ)) '' K') :=
    hbox.of_isClosed_subset (isClosedEmbedding_coe.isClosedMap K' hK') hsub
  have := isClosedEmbedding_coe.isCompact_preimage himg
  rwa [Set.preimage_image_eq _ isClosedEmbedding_coe.injective] at this

/-- Boundedness propagates through generators: if `U` is generated over `A` by `s`, the elements
of `s` are bounded on `K'`, and `K'` lies over a compact set `K`, then every element of `U` is
bounded on `K'`. -/
theorem forall_bounded_of_gen {U : Type*} [CommRing U] [Algebra A U] {K : Set (RealPt A)}
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

/-! ### Finitely generated `ℚ`-algebras -/

section Generators

variable [Algebra ℚ A] {m : ℕ} (a : Fin m → A)

omit [Algebra ℚ A] in
/-- The coordinates `z ↦ (z a₁, …, z a_m)` of real points with respect to a family `a`. -/
def evalGens (z : RealPt A) : Fin m → ℝ := fun i => z (a i)

omit [Algebra ℚ A] in
lemma continuous_evalGens : Continuous (evalGens a) :=
  continuous_pi fun i => continuous_eval (a i)

/-- The real zero set in `ℝ^m` of the relations among the `aᵢ`. -/
def relZeroSet : Set (Fin m → ℝ) :=
  {p | ∀ P ∈ RingHom.ker (MvPolynomial.aeval (R := ℚ) a), MvPolynomial.aeval p P = 0}

/-- Polynomials with rational coefficients are continuous functions on `ℝ^m`. -/
lemma continuous_aeval_rat (P : MvPolynomial (Fin m) ℚ) :
    Continuous fun p : Fin m → ℝ => MvPolynomial.aeval p P := by
  have : (fun p : Fin m → ℝ => MvPolynomial.aeval p P) =
      fun p => MvPolynomial.eval p (MvPolynomial.map (algebraMap ℚ ℝ) P) := by
    funext p
    simp [MvPolynomial.aeval_def, MvPolynomial.eval_map]
  rw [this]
  exact MvPolynomial.continuous_eval _

/-- A real point, viewed as a `ℚ`-algebra homomorphism. -/
def toAlgHom (z : RealPt A) : A →ₐ[ℚ] ℝ := (toHom z).toRatAlgHom

@[simp] lemma toAlgHom_apply (z : RealPt A) (b : A) : toAlgHom z b = z b := rfl

/-- The value of a real point at a polynomial expression in the `aᵢ`. -/
lemma apply_aeval (z : RealPt A) (P : MvPolynomial (Fin m) ℚ) :
    z (MvPolynomial.aeval a P) = MvPolynomial.aeval (evalGens a z) P := by
  exact MvPolynomial.comp_aeval_apply (R := ℚ) (f := a) (toAlgHom z) P

variable {a}

/-- Real points are determined by their values on generators. -/
lemma evalGens_injective (hgen : Algebra.adjoin ℚ (Set.range a) = ⊤) :
    Function.Injective (evalGens a) := by
  intro z w h
  have : toAlgHom z = toAlgHom w :=
    AlgHom.ext_of_adjoin_eq_top hgen (by
      rintro _ ⟨i, rfl⟩
      exact congrFun h i)
  ext b
  exact DFunLike.congr_fun this b

/-- **Real points of a finitely generated `ℚ`-algebra.** If `A = ℚ[a₁, …, a_m]`, the map
`z ↦ (z a₁, …, z a_m)` is a topological embedding. -/
theorem isEmbedding_evalGens (hgen : Algebra.adjoin ℚ (Set.range a) = ⊤) :
    IsEmbedding (evalGens a) := by
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.1 (continuous_evalGens a)) ?_⟩,
    evalGens_injective hgen⟩
  -- every evaluation map is continuous for the topology induced by `evalGens a`
  let tI : TopologicalSpace (RealPt A) := TopologicalSpace.induced (evalGens a) inferInstance
  have hcont : Continuous (fun z : RealPt A => (z : A → ℝ)) := by
    refine continuous_pi fun b => ?_
    obtain ⟨P, rfl⟩ : ∃ P, MvPolynomial.aeval a P = b := by
      have hb : b ∈ Algebra.adjoin ℚ (Set.range a) := by rw [hgen]; trivial
      rw [← MvPolynomial.aeval_range] at hb
      exact hb
    have : (fun z : RealPt A => (z : A → ℝ) (MvPolynomial.aeval a P)) =
        (fun p => MvPolynomial.aeval p P) ∘ evalGens a := by
      funext z; exact apply_aeval a z P
    rw [this]
    exact (continuous_aeval_rat P).comp continuous_induced_dom
  exact continuous_iff_le_induced.1 hcont

/-- The image of `z ↦ (z a₁, …, z a_m)` is the real zero set of the relations among the `aᵢ`. -/
theorem range_evalGens (hgen : Algebra.adjoin ℚ (Set.range a) = ⊤) :
    Set.range (evalGens a) = relZeroSet a := by
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := ℚ) a) := by
    intro b
    have hb : b ∈ Algebra.adjoin ℚ (Set.range a) := by rw [hgen]; trivial
    rw [← MvPolynomial.aeval_range] at hb
    exact hb
  ext p
  constructor
  · rintro ⟨z, rfl⟩ P hP
    rw [← apply_aeval, RingHom.mem_ker.1 hP, map_zero]
  · intro hp
    let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
    let φ : MvPolynomial (Fin m) ℚ ⧸ RingHom.ker (MvPolynomial.aeval (R := ℚ) a) →ₐ[ℚ] ℝ :=
      Ideal.Quotient.liftₐ _ (MvPolynomial.aeval p) (fun P hP => hp P hP)
    refine ⟨ofHom (φ.comp e.symm.toAlgHom).toRingHom, funext fun i => ?_⟩
    have : e.symm (a i) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
      rw [AlgEquiv.symm_apply_eq]
      simp [e]
    show φ (e.symm (a i)) = p i
    rw [this]
    exact MvPolynomial.aeval_X (R := ℚ) p i

/-- **Compactness criterion.** If `A = ℚ[a₁, …, a_m]`, a set of real points is compact if and only
if it is closed and the generators `a₁, …, a_m` are bounded on it. -/
theorem isCompact_iff (hgen : Algebra.adjoin ℚ (Set.range a) = ⊤) (K : Set (RealPt A)) :
    IsCompact K ↔ IsClosed K ∧ ∀ i, ∃ C : ℝ, ∀ z ∈ K, |z (a i)| ≤ C := by
  constructor
  · intro hK
    refine ⟨hK.isClosed, fun i => ?_⟩
    obtain ⟨C, hC⟩ := (hK.image (continuous_eval (a i))).isBounded.exists_norm_le
    exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC _ ⟨z, hz, rfl⟩⟩
  · rintro ⟨hcl, hb⟩
    refine isCompact_of_forall_bounded hcl fun b => ?_
    have hb' : b ∈ Algebra.adjoin ℚ (Set.range a) := by rw [hgen]; trivial
    induction hb' using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hb i
    | algebraMap q =>
      refine ⟨|(q : ℝ)|, fun w _ => le_of_eq ?_⟩
      rw [← eq_ratCast (toHom w |>.comp (algebraMap ℚ A)) q]
      rfl
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

end Generators

end RealPt

/-! ## Monotone surjections -/

/-- A *monotone surjection*: a continuous surjection all of whose fibres are connected. (In the
applications the spaces are moreover compact Hausdorff; these hypotheses are imposed separately
where they are needed.) -/
structure IsMonotoneSurjection {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) : Prop where
  continuous : Continuous q
  surjective : Function.Surjective q
  isConnected_fiber : ∀ y, IsConnected (q ⁻¹' {y})

/-- `q` restricts to a monotone surjection `K' → K`. -/
def IsMonotoneSurjOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (K' : Set X) (K : Set Y) : Prop :=
  ∃ h : Set.MapsTo q K' K, IsMonotoneSurjection (h.restrict q K' K)

/-- The identity is a monotone surjection `K → K`. -/
lemma IsMonotoneSurjOn.id {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsMonotoneSurjOn (fun z : X => z) K K := by
  refine ⟨mapsTo_id K, ⟨continuous_id.subtype_map _, fun w => ⟨w, rfl⟩, fun z => ?_⟩⟩
  have : (Set.MapsTo.restrict (fun z : X => z) K K (mapsTo_id K)) ⁻¹' {z} = {z} := by
    ext w
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h; exact Subtype.ext (congrArg Subtype.val h)
    · intro h; subst h; rfl
  rw [this]
  exact isConnected_singleton

end BezoutCounterexample
