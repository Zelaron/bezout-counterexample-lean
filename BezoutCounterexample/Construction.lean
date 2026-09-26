import BezoutCounterexample.Topology

/-!
# Section 5: construction of the Bézout domain (Construction 5.1, Proposition 5.2)

From Proposition 4.6 of the paper for coprime pairs (`CoprimePairPE`, implied by
`PrincipalizationExtension`), we construct injections
`A₀ ↪ A₁ ↪ A₂ ↪ ⋯` of smooth finitely generated factorial `ℚ`-domains together with compact sets
`Kₙ ⊂ Spec(Aₙ)(ℝ)` such that the pullback of the Möbius bundle to every `Kₙ` is nonorientable,
and put `R = ⋃ Aₙ` (a direct limit). Everything here is parametrized by a proof
`hPE : CoprimePairPE`; such a proof is `coprimePairPE_holds` (`MainTheorem.lean`), obtained from
`Principalization.principalizationExtension`.

As in Construction 5.1, one pair is processed per stage, using the Cantor pairing function: at
stage `n = pair(i, j)` we process the image in `Aₙ` of `ηᵢ(j)`, so every pair of elements of every
`Aᵢ` is processed at some later stage.

* `isCompact_K₀`: the circle is compact.
* `nonorientable_pullback`: nonorientability is preserved along monotone surjections
  (Lemma 2.1), which gives (5.2).
* `R`, `R.isDomain`, `R.isBezout`, `R.countable`, `R.Δ_ne_zero`, `R.Δ_not_isUnit`
  (Proposition 5.2).
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology

/-! ### Preliminaries -/

instance SmoothFactorialDomain.countable (A : SmoothFactorialDomain) : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType ℚ A)
  exact hf.countable

/-- `A₀ = ℚ[x,y]` as a smooth factorial domain. -/
def A₀SFD : SmoothFactorialDomain := ⟨A₀⟩

/-- Evaluation of `A₀ = ℚ[x,y]` at a point of `ℝ²`. -/
def evalPt (p : Fin 2 → ℝ) : RealPt A₀ :=
  RealPt.ofHom (MvPolynomial.aeval p : A₀ →ₐ[ℚ] ℝ).toRingHom

@[simp] lemma evalPt_x (p : Fin 2 → ℝ) : evalPt p x = p 0 := by simp [evalPt, x]

@[simp] lemma evalPt_y (p : Fin 2 → ℝ) : evalPt p y = p 1 := by simp [evalPt, y]

lemma continuous_evalPt : Continuous evalPt := by
  rw [RealPt.continuous_iff]
  intro q
  have : (fun p => evalPt p q) =
      fun p : Fin 2 → ℝ => MvPolynomial.eval p (MvPolynomial.map (algebraMap ℚ ℝ) q) := by
    funext p
    simp [evalPt, MvPolynomial.aeval_def, MvPolynomial.eval_map]
  rw [this]
  exact MvPolynomial.continuous_eval _

lemma Δ_eval (z : RealPt A₀) : z Δ = z x ^ 2 + z y ^ 2 - 1 := by
  simp [Δ, map_sub, map_add, map_pow, map_one]

/-- The circle `K₀` is compact. -/
theorem isCompact_K₀ : IsCompact K₀ := by
  have hS : IsCompact {p : Fin 2 → ℝ | p 0 ^ 2 + p 1 ^ 2 = 1} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by fun_prop) continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun p hp => ?_⟩
      simp only [mem_ofPred_eq] at hp
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, abs_le]
      fin_cases i <;> simp <;> constructor <;> nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  have : K₀ = evalPt '' {p : Fin 2 → ℝ | p 0 ^ 2 + p 1 ^ 2 = 1} := by
    ext z
    constructor
    · intro hz
      refine ⟨![z x, z y], ?_, ?_⟩
      · have : z Δ = 0 := hz
        rw [Δ_eval] at this
        simp only [mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      · exact realPt_A₀_ext (by simp) (by simp)
    · rintro ⟨p, hp, rfl⟩
      show evalPt p Δ = 0
      rw [Δ_eval, evalPt_x, evalPt_y]
      simp only [mem_ofPred_eq] at hp
      linarith
  rw [this]
  exact hS.image continuous_evalPt

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

/-- Nonorientability of `z ↦ im M(z a, z b)` is preserved under pullback along a monotone
surjection (this is how Lemma 2.1 is used to obtain (5.2)). -/
theorem nonorientable_pullback {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a b : A)
    {K : Set (RealPt A)} {K' : Set (RealPt B)} (hK' : IsCompact K')
    (hmono : IsMonotoneSurjOn (RealPt.comap f) K' K) (hcirc : ∀ z ∈ K, z a ^ 2 + z b ^ 2 = 1)
    (h : ¬ LineFieldOrientable (fun z : K => z.1 a) (fun z : K => z.1 b)) :
    ¬ LineFieldOrientable (fun z : K' => z.1 (f a)) (fun z : K' => z.1 (f b)) := by
  obtain ⟨hmaps, hq⟩ := hmono
  have := isCompact_iff_compactSpace.1 hK'
  intro h'
  exact h (orientation_descent hq (fun z : K => z.1 a) (fun z : K => z.1 b)
    (fun z => hcirc z.1 z.2) h')

/-! ### Stages of the construction -/

/-- The data at a stage of Construction 5.1: a smooth factorial domain `A` with an injection
`ι : A₀ ↪ A`, a compact set `K ⊂ Spec(A)(ℝ)` lying over the circle, on which the pullback of the
Möbius bundle is nonorientable, and an enumeration `e i` of (the image in `A` of) `Aᵢ × Aᵢ`. -/
structure Stage where
  A : SmoothFactorialDomain
  ι : A₀ →ₐ[ℚ] A
  K : Set (RealPt A)
  e : ℕ → ℕ → A × A
  ι_injective : Function.Injective ι
  K_compact : IsCompact K
  K_circle : ∀ z ∈ K, z (ι Δ) = 0
  nonorientable : ¬ LineFieldOrientable (fun z : K => z.1 (ι x)) (fun z : K => z.1 (ι y))

lemma Stage.circle (S : Stage) (z : RealPt S.A) (hz : z ∈ S.K) :
    z (S.ι x) ^ 2 + z (S.ι y) ^ 2 = 1 := by
  have h := S.K_circle z hz
  have : z (S.ι Δ) = z (S.ι x) ^ 2 + z (S.ι y) ^ 2 - 1 := by
    simp [Δ, map_sub, map_add, map_pow, map_one]
  linarith

/-- The pair processed at stage `n`. -/
def Stage.pair (S : Stage) (n : ℕ) : S.A × S.A := S.e n.unpair.1 n.unpair.2

/-- The result of one step of the construction, starting from stage `S` at time `n`. -/
structure StepData (n : ℕ) (S : Stage) where
  next : Stage
  map : S.A →ₐ[ℚ] next.A
  map_injective : Function.Injective map
  ι_comp : next.ι = map.comp S.ι
  e_old : ∀ i ≤ n, ∀ j, next.e i j = Prod.map map map (S.e i j)
  e_new : Function.Surjective (next.e (n + 1))
  principal : (Ideal.span {map (S.pair n).1, map (S.pair n).2} : Ideal next.A).IsPrincipal

/-- The updated enumeration. -/
def newEnum {A B : Type*} (n : ℕ) (f : A → B) (e : ℕ → ℕ → A × A) (η : ℕ → B × B) :
    ℕ → ℕ → B × B :=
  fun i j => if i ≤ n then Prod.map f f (e i j) else η j

/-- A step, given an extension `A → A'` principalizing the processed pair, with a compact set
`K'` mapping monotonically onto `K`. -/
def mkStep (n : ℕ) (S : Stage) (A' : SmoothFactorialDomain) (f : S.A →ₐ[ℚ] A')
    (K' : Set (RealPt A')) (hf : Function.Injective f) (hK' : IsCompact K')
    (hmono : IsMonotoneSurjOn (RealPt.comap (f : S.A →+* A')) K' S.K)
    (hprinc : (Ideal.span {f (S.pair n).1, f (S.pair n).2} : Ideal A').IsPrincipal) :
    StepData n S where
  next :=
    { A := A'
      ι := f.comp S.ι
      K := K'
      e := newEnum n f S.e (Classical.choose (exists_surjective_nat (A' × A')))
      ι_injective := hf.comp S.ι_injective
      K_compact := hK'
      K_circle := fun z hz => by
        have := S.K_circle _ (hmono.1 hz)
        simpa using this
      nonorientable := by
        have := nonorientable_pullback (f : S.A →+* A') (S.ι x) (S.ι y) hK' hmono
          (fun z hz => S.circle z hz) S.nonorientable
        simpa using this }
  map := f
  map_injective := hf
  ι_comp := rfl
  e_old i hi j := by simp [newEnum, hi]
  e_new := by
    have h := Classical.choose_spec (exists_surjective_nat (A' × A'))
    show Function.Surjective
      (newEnum n f S.e (Classical.choose (exists_surjective_nat (A' × A'))) (n + 1))
    have : newEnum n f S.e (Classical.choose (exists_surjective_nat (A' × A'))) (n + 1) =
        Classical.choose (exists_surjective_nat (A' × A')) := by
      funext j; simp [newEnum]
    rw [this]; exact h
  principal := hprinc

/-- **Proposition 4.6 for coprime pairs**: the conclusion of `PrincipalizationExtension` for
ideals `(a, b)` with `a, b` coprime and nonzero. This is all the construction needs. -/
def CoprimePairPE : Prop :=
  ∀ (A : SmoothFactorialDomain) (a b : A) (K : Set (RealPt A)),
    IsRelPrime a b → a ≠ 0 → b ≠ 0 → IsCompact K →
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ ((Ideal.span {a, b}).map f).IsPrincipal ∧ IsCompact K' ∧
        IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K

theorem PrincipalizationExtension.coprimePair (h : PrincipalizationExtension) : CoprimePairPE :=
  fun A a b K _ ha _ hK => h A (Ideal.span {a, b}) K
    (fun h0 => ha (by
      have : a ∈ (⊥ : Ideal A) := h0 ▸ Ideal.subset_span (by simp)
      simpa using this))
    (Submodule.fg_span ((Set.finite_singleton _).insert _)) hK

/-- From the coprime case, Proposition 4.6 follows for every pair (extract a gcd). -/
theorem CoprimePairPE.pair (hPE : CoprimePairPE) (A : SmoothFactorialDomain) (a b : A)
    (K : Set (RealPt A)) (hK : IsCompact K) :
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ ((Ideal.span {a, b}).map f).IsPrincipal ∧ IsCompact K' ∧
        IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K := by
  classical
  by_cases hb : b = 0
  · refine ⟨A, AlgHom.id ℚ A, K, Function.injective_id, ⟨⟨a, ?_⟩⟩, hK, IsMonotoneSurjOn.id K⟩
    rw [hb, Ideal.map_span, Set.image_pair, Set.pair_comm]
    simp
  by_cases ha : a = 0
  · refine ⟨A, AlgHom.id ℚ A, K, Function.injective_id, ⟨⟨b, ?_⟩⟩, hK, IsMonotoneSurjOn.id K⟩
    rw [ha, Ideal.map_span, Set.image_pair]
    simp
  obtain ⟨a', b', c, hcop, rfl, rfl⟩ := UniqueFactorizationMonoid.exists_reduced_factors' a b hb
  have ha' : a' ≠ 0 := by rintro rfl; exact ha (mul_zero c)
  have hb' : b' ≠ 0 := by rintro rfl; exact hb (mul_zero c)
  obtain ⟨A', f, K', hinj, ⟨⟨g, hg⟩⟩, hK', hmono⟩ := hPE A a' b' K hcop ha' hb' hK
  refine ⟨A', f, K', hinj, ⟨⟨f c * g, ?_⟩⟩, hK', hmono⟩
  have hsplit : (Ideal.span {c * a', c * b'} : Ideal A) = Ideal.span {c} * Ideal.span {a', b'} := by
    rw [Ideal.span_mul_span, Set.singleton_mul, Set.image_pair]
  rw [hsplit, Ideal.map_mul, hg, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_mul_span_singleton]

variable (hPE : CoprimePairPE)

/-- The initial stage: `A₀ = ℚ[x,y]` and the circle `K₀`. -/
def initialStage : Stage where
  A := A₀SFD
  ι := AlgHom.id ℚ A₀
  K := K₀
  e := fun _ => Classical.choose (exists_surjective_nat (A₀ × A₀))
  ι_injective := Function.injective_id
  K_compact := isCompact_K₀
  K_circle := fun _ hz => hz
  nonorientable := L₀_nonorientable

/-- One step of Construction 5.1: apply Proposition 4.6 (for pairs, reduced to coprime pairs by
extracting a gcd) to the pair processed at time `n`, and carry along the compact set. -/
def step (n : ℕ) (S : Stage) : StepData n S := by
  classical
  have h := hPE.pair S.A (S.pair n).1 (S.pair n).2 S.K S.K_compact
  have h1 := Classical.choose_spec h
  have h2 := Classical.choose_spec h1
  have h3 := Classical.choose_spec h2
  refine mkStep n S (Classical.choose h) (Classical.choose h1) (Classical.choose h2)
    h3.1 h3.2.2.1 h3.2.2.2 ?_
  have := h3.2.1
  rwa [Ideal.map_span, Set.image_pair] at this

/-- The stages `(Aₙ, Kₙ)` of Construction 5.1. -/
def stage : ℕ → Stage := fun n => Nat.rec (initialStage) (fun n S => (step hPE n S).next) n

lemma stage_zero : stage hPE 0 = initialStage := rfl

lemma stage_succ (n : ℕ) : stage hPE (n + 1) = (step hPE n (stage hPE n)).next := rfl

/-- The ring `Aₙ`. -/
abbrev G (n : ℕ) : Type := (stage hPE n).A

/-- The injection `Aₙ ↪ Aₙ₊₁`. -/
def trans (n : ℕ) : G hPE n →ₐ[ℚ] G hPE (n + 1) := (step hPE n (stage hPE n)).map

lemma trans_injective (n : ℕ) : Function.Injective (trans hPE n) :=
  (step hPE n (stage hPE n)).map_injective

lemma ι_succ (n : ℕ) : (stage hPE (n + 1)).ι = (trans hPE n).comp (stage hPE n).ι :=
  (step hPE n (stage hPE n)).ι_comp

/-- The composite `Aᵢ → Aⱼ` for `i ≤ j`. -/
def transLE {i j : ℕ} (h : i ≤ j) (a : G hPE i) : G hPE j :=
  Nat.leRecOn h (fun {k} (b : G hPE k) => trans hPE k b) a

lemma transLE_self (i : ℕ) (a : G hPE i) : transLE hPE (le_refl i) a = a :=
  Nat.leRecOn_self _

lemma transLE_succ {i j : ℕ} (h : i ≤ j) (a : G hPE i) :
    transLE hPE (h.trans (Nat.le_succ j)) a = trans hPE j (transLE hPE h a) :=
  Nat.leRecOn_succ h _

lemma transLE_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : G hPE i) :
    transLE hPE (hij.trans hjk) a = transLE hPE hjk (transLE hPE hij a) :=
  Nat.leRecOn_trans hij hjk _

lemma transLE_one (i j : ℕ) (h : i ≤ j) : transLE hPE h 1 = 1 := by
  induction j, h using Nat.le_induction with
  | base => exact transLE_self hPE i 1
  | succ k hik ih => rw [transLE_succ hPE hik, ih, map_one]

lemma transLE_zero (i j : ℕ) (h : i ≤ j) : transLE hPE h 0 = 0 := by
  induction j, h using Nat.le_induction with
  | base => exact transLE_self hPE i 0
  | succ k hik ih => rw [transLE_succ hPE hik, ih, map_zero]

lemma transLE_mul (i j : ℕ) (h : i ≤ j) (a b : G hPE i) :
    transLE hPE h (a * b) = transLE hPE h a * transLE hPE h b := by
  induction j, h using Nat.le_induction with
  | base => simp only [transLE_self]
  | succ k hik ih => rw [transLE_succ hPE hik, transLE_succ hPE hik, transLE_succ hPE hik, ih,
      map_mul]

lemma transLE_add (i j : ℕ) (h : i ≤ j) (a b : G hPE i) :
    transLE hPE h (a + b) = transLE hPE h a + transLE hPE h b := by
  induction j, h using Nat.le_induction with
  | base => simp only [transLE_self]
  | succ k hik ih => rw [transLE_succ hPE hik, transLE_succ hPE hik, transLE_succ hPE hik, ih,
      map_add]

/-- The composite `Aᵢ → Aⱼ` as a ring homomorphism. -/
def transHom (i j : ℕ) (h : i ≤ j) : G hPE i →+* G hPE j where
  toFun := transLE hPE h
  map_one' := transLE_one hPE i j h
  map_mul' := transLE_mul hPE i j h
  map_zero' := transLE_zero hPE i j h
  map_add' := transLE_add hPE i j h

lemma transHom_injective (i j : ℕ) (h : i ≤ j) : Function.Injective (transHom hPE i j h) :=
  Nat.leRecOn_injective h _ (fun k => trans_injective hPE k)

instance directedSystem : DirectedSystem (G hPE) fun i j h => ⇑(transHom hPE i j h) where
  map_self i a := transLE_self hPE i a
  map_map _ _ _ hij hjk a := (transLE_trans hPE hij hjk a).symm

/-- **The ring `R = ⋃ₙ Aₙ`** (equation (5.1)), as a direct limit. -/
def R : Type := Ring.DirectLimit (G hPE) fun i j h => ⇑(transHom hPE i j h)

namespace R

instance : CommRing (R hPE) := inferInstanceAs (CommRing (Ring.DirectLimit _ _))

/-- The inclusion `Aₙ ↪ R`. -/
def of (n : ℕ) : G hPE n →+* R hPE := Ring.DirectLimit.of (G hPE) _ n

lemma of_transHom {i j : ℕ} (h : i ≤ j) (a : G hPE i) :
    of hPE j (transHom hPE i j h a) = of hPE i a :=
  Ring.DirectLimit.of_f h a

lemma of_trans (n : ℕ) (a : G hPE n) : of hPE (n + 1) (trans hPE n a) = of hPE n a := by
  have h := of_transHom hPE (Nat.le_succ n) a
  have h2 : transHom hPE n (n + 1) (Nat.le_succ n) a = trans hPE n a := by
    show transLE hPE _ a = _
    exact (transLE_succ hPE (le_refl n) a).trans (congrArg _ (transLE_self hPE n a))
  rwa [h2] at h

lemma of_injective (n : ℕ) : Function.Injective (of hPE n) :=
  Ring.DirectLimit.of_injective (G := G hPE) (fun i j h => transHom hPE i j h)
    (fun i j h => transHom_injective hPE i j h) n

lemma exists_of (r : R hPE) : ∃ n a, of hPE n a = r := Ring.DirectLimit.exists_of r

/-- Any finite family of elements of `R` comes from a single stage. -/
lemma exists_of_fin (k : ℕ) (v : Fin k → R hPE) :
    ∃ (n : ℕ) (w : Fin k → G hPE n), ∀ t, of hPE n (w t) = v t := by
  induction k with
  | zero => exact ⟨0, Fin.elim0, fun t => Fin.elim0 t⟩
  | succ k ih =>
    obtain ⟨n, w, hw⟩ := ih (fun t => v t.castSucc)
    obtain ⟨m, a, ha⟩ := exists_of hPE (v (Fin.last k))
    refine ⟨max n m, Fin.lastCases (transHom hPE m (max n m) (le_max_right n m) a)
      (fun t => transHom hPE n (max n m) (le_max_left n m) (w t)), fun t => ?_⟩
    induction t using Fin.lastCases with
    | last => simp only [Fin.lastCases_last, of_transHom, ha]
    | cast t => simp only [Fin.lastCases_castSucc, of_transHom, hw]

/-- The inclusion `A₀ ↪ R`. -/
def ι : A₀ →+* R hPE := of hPE 0

lemma of_comp_ι (n : ℕ) : (of hPE n).comp ((stage hPE n).ι : A₀ →+* G hPE n) = ι hPE := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    ext a
    · simp only [RingHom.comp_apply]
      rw [ι_succ]
      simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply]
      exact of_trans hPE n _
    · simp only [RingHom.comp_apply]
      rw [ι_succ]
      simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply]
      exact of_trans hPE n _

lemma of_ι (n : ℕ) (a : A₀) : of hPE n ((stage hPE n).ι a) = ι hPE a :=
  congrArg (fun g : A₀ →+* R hPE => g a) (of_comp_ι hPE n)

lemma ι_injective : Function.Injective (ι hPE) := of_injective hPE 0

instance : Nontrivial (R hPE) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have : of hPE 0 0 = of hPE 0 1 := by simpa using h
  exact zero_ne_one (of_injective hPE 0 this)

instance : IsDomain (R hPE) := by
  have : NoZeroDivisors (R hPE) := ⟨fun {a b} hab => by
      obtain ⟨n, w, hw⟩ := exists_of_fin hPE 2 ![a, b]
      have ha : of hPE n (w 0) = a := hw 0
      have hb : of hPE n (w 1) = b := hw 1
      have : w 0 * w 1 = 0 := by
        apply of_injective hPE n
        rw [map_mul, ha, hb, hab, map_zero]
      rcases mul_eq_zero.1 this with h | h
      · left; rw [← ha, h, map_zero]
      · right; rw [← hb, h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

/-- `R` is countable. -/
instance : Countable (R hPE) := by
  have : Function.Surjective fun p : Σ n, G hPE n => of hPE p.1 p.2 := by
    intro r
    obtain ⟨n, a, h⟩ := exists_of hPE r
    exact ⟨⟨n, a⟩, h⟩
  exact this.countable

/-! #### Enumeration bookkeeping -/

lemma e_zero_surjective : Function.Surjective ((stage hPE 0).e 0) :=
  Classical.choose_spec (exists_surjective_nat (A₀ × A₀))

lemma e_diag_surjective (m : ℕ) : Function.Surjective ((stage hPE m).e m) := by
  cases m with
  | zero => exact e_zero_surjective hPE
  | succ m => exact (step hPE m (stage hPE m)).e_new

lemma e_transport (m : ℕ) (j : ℕ) :
    ∀ n (h : m ≤ n), (stage hPE n).e m j =
      Prod.map (transHom hPE m n h) (transHom hPE m n h) ((stage hPE m).e m j) := by
  intro n h
  induction n, h using Nat.le_induction with
  | base =>
    ext <;> simp [transHom, transLE_self]
  | succ k hmk ih =>
    show (step hPE k (stage hPE k)).next.e m j = _
    rw [(step hPE k (stage hPE k)).e_old m hmk j, ih]
    ext <;> simp only [Prod.map_fst, Prod.map_snd] <;>
      exact (transLE_succ hPE hmk _).symm

/-- **Proposition 5.2 (Bézout).** Every two-generated ideal of `R` is principal. -/
instance isBezout : IsBezout (R hPE) := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  obtain ⟨m, w, hw⟩ := exists_of_fin hPE 2 ![a, b]
  obtain ⟨j, hj⟩ := e_diag_surjective hPE m (w 0, w 1)
  set n := Nat.pair m j
  have hmn : m ≤ n := Nat.left_le_pair m j
  have hpair : (stage hPE n).pair n =
      (transHom hPE m n hmn (w 0), transHom hPE m n hmn (w 1)) := by
    rw [Stage.pair, Nat.unpair_pair, e_transport hPE m j n hmn, hj]
    rfl
  obtain ⟨g, hg⟩ := (step hPE n (stage hPE n)).principal
  let g' : G hPE (n + 1) := g
  have hg' : (Ideal.span {trans hPE n ((stage hPE n).pair n).1,
      trans hPE n ((stage hPE n).pair n).2} : Ideal (G hPE (n + 1))) =
      Ideal.span {g'} := hg
  have hmap := congrArg (Ideal.map (of hPE (n + 1))) hg'
  rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton, hpair, of_trans,
    of_trans, of_transHom, of_transHom, hw 0, hw 1] at hmap
  exact ⟨⟨of hPE (n + 1) g', by simpa using hmap⟩⟩

/-- The real points of the stage `Aₙ` lying in `Kₙ` form a nonempty set. -/
lemma K_nonempty (n : ℕ) : (stage hPE n).K.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have he : IsEmpty (stage hPE n).K := Set.isEmpty_coe_sort.2 h
  apply (stage hPE n).nonorientable
  exact ⟨fun z => (he.false z).elim, continuous_of_const fun z => (he.false z).elim,
    fun z => (he.false z).elim⟩

/-- **Proposition 5.2.** `Δ` is a nonzero element of `R`. -/
lemma Δ_ne_zero : ι hPE Δ ≠ 0 := by
  intro h
  have : (Δ : A₀) = 0 := ι_injective hPE (by rw [h, map_zero])
  have h2 := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) this
  simp [Δ, x, y] at h2

/-- **Proposition 5.2.** `Δ` is not a unit of `R`. -/
lemma Δ_not_isUnit : ¬ IsUnit (ι hPE Δ) := by
  rintro ⟨u, hu⟩
  obtain ⟨n, w, hw⟩ := exists_of_fin hPE 1 ![(u⁻¹ : (R hPE)ˣ)]
  have h1 : (stage hPE n).ι Δ * w 0 = 1 := by
    apply of_injective hPE n
    rw [map_mul, map_one, of_ι, hw 0, ← hu]
    simp
  obtain ⟨z, hz⟩ := K_nonempty hPE n
  have h2 := congrArg z h1
  rw [map_mul, map_one, (stage hPE n).K_circle z hz, zero_mul] at h2
  exact zero_ne_one h2

/-- `R` is a `ℚ`-algebra, hence of characteristic zero. -/
instance : Algebra ℚ (R hPE) := ((ι hPE).comp (algebraMap ℚ A₀)).toAlgebra

instance : CharZero (R hPE) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (R hPE)).injective

/-- `x` and `y` remain algebraically independent over `ℚ` in `R`. -/
lemma algebraicIndependent : AlgebraicIndependent ℚ ![ι hPE x, ι hPE y] := by
  rw [algebraicIndependent_iff_injective_aeval]
  have : (MvPolynomial.aeval ![ι hPE x, ι hPE y] : A₀ →ₐ[ℚ] R hPE).toRingHom = ι hPE := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C]
      rfl
    · intro i
      fin_cases i <;> simp [x, y]
  intro p q hpq
  apply ι_injective hPE
  rw [← this]
  exact hpq

end R

end BezoutCounterexample
