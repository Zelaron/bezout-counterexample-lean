import BezoutCounterexample.MainTheorem

/-!
# Section 6: consequences and examples

* `HasSmithNormalForm.map`: Smith normal forms are preserved by ring homomorphisms.
* `countable_reduction` (Proposition 6.5, `prop:countable-reduction`): a matrix without Smith
  normal form over a Bézout domain has no Smith normal form over some countable Bézout subdomain.
* `IsBezout.isSemihereditary`: every Bézout domain is semihereditary.
* `HasCountableCharacter`, `IsSemihereditary`, `IsElementaryDivisorRing`. Corollary 6.4
  (`cor:not-countable-character`), together with the case of Couchot's theorem it needs, is in
  `Couchot.lean`.
* `exampleC_*`: the countable domain `ℚ[t, z₁, z₂, …]` has uncountably many maximal ideals
  containing `t`.
-/

noncomputable section

namespace BezoutCounterexample

open Set

/-! ### Smith normal forms along ring homomorphisms -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

theorem IsSmithNormalForm.map {m n : ℕ} {D : Matrix (Fin m) (Fin n) R} (h : IsSmithNormalForm D)
    (f : R →+* S) : IsSmithNormalForm (D.map f) := by
  obtain ⟨d, hd, hdiv⟩ := h
  refine ⟨fun k => f (d k), fun i j => ?_, fun k hk => map_dvd f (hdiv k hk)⟩
  rw [Matrix.map_apply, hd]
  split_ifs <;> simp

theorem HasSmithNormalForm.map {m n : ℕ} {F : Matrix (Fin m) (Fin n) R}
    (h : HasSmithNormalForm F) (f : R →+* S) : HasSmithNormalForm (F.map f) := by
  obtain ⟨G, ⟨P, Q, hPQ⟩, hG⟩ := h
  refine ⟨G.map f, ⟨Matrix.GeneralLinearGroup.map f P, Matrix.GeneralLinearGroup.map f Q, ?_⟩,
    hG.map f⟩
  rw [← hPQ, Matrix.map_mul, Matrix.map_mul]
  rfl

end Map

/-! ### Proposition 6.5: countable reduction -/

section CountableReduction

variable {D : Type*} [CommRing D]

lemma countable_closure {s : Set D} (hs : s.Countable) :
    (Subring.closure s : Set D).Countable := by
  have h1 : (Subring.closure s : Set D) = (Algebra.adjoin ℤ s : Set D) := by
    rw [Algebra.adjoin_int]; rfl
  rw [h1, Algebra.adjoin_eq_range]
  have := hs.to_subtype
  exact Set.countable_range _

/-- In a Bézout domain every pair `(a, b)` has witnesses `g = r a + s b`, `a = g c`, `b = g d`. -/
lemma exists_bezout_witness [IsBezout D] (a b : D) :
    ∃ w : Fin 5 → D, w 0 = w 1 * a + w 2 * b ∧ a = w 0 * w 3 ∧ b = w 0 * w 4 := by
  obtain ⟨g, hg⟩ := (IsBezout.iff_span_pair_isPrincipal.1 inferInstance a b).principal
  have hgmem : g ∈ Ideal.span {a, b} := by rw [hg]; exact Submodule.mem_span_singleton_self g
  obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 hgmem
  have ha : a ∈ Ideal.span {a, b} := Ideal.subset_span (by simp)
  have hb : b ∈ Ideal.span {a, b} := Ideal.subset_span (by simp)
  rw [hg] at ha hb
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ha
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hb
  refine ⟨![g, r, s, c, d], ?_, ?_, ?_⟩
  · simp [hrs]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_three]
    rw [← hc, smul_eq_mul, mul_comm]; rfl
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_four]
    rw [← hd, smul_eq_mul, mul_comm]; rfl

variable [IsBezout D]

/-- A choice of Bézout witnesses. -/
def witness (p : D × D) : Fin 5 → D := Classical.choose (exists_bezout_witness p.1 p.2)

lemma witness_spec (a b : D) :
    witness (a, b) 0 = witness (a, b) 1 * a + witness (a, b) 2 * b ∧
      a = witness (a, b) 0 * witness (a, b) 3 ∧ b = witness (a, b) 0 * witness (a, b) 4 :=
  Classical.choose_spec (exists_bezout_witness a b)

/-- The chain of countable subrings `S₀ ⊂ S₁ ⊂ ⋯` of the proof of Proposition 6.5. -/
def reductionChain (s₀ : Set D) : ℕ → Subring D
  | 0 => Subring.closure s₀
  | k + 1 => Subring.closure ((reductionChain s₀ k : Set D) ∪
      ⋃ p ∈ (reductionChain s₀ k : Set D) ×ˢ (reductionChain s₀ k : Set D), Set.range (witness p))

lemma reductionChain_le_succ (s₀ : Set D) (k : ℕ) :
    reductionChain s₀ k ≤ reductionChain s₀ (k + 1) := fun _ hz =>
  Subring.subset_closure (Or.inl hz)

lemma reductionChain_mono (s₀ : Set D) : Monotone (reductionChain s₀) :=
  monotone_nat_of_le_succ (reductionChain_le_succ s₀)

lemma reductionChain_countable {s₀ : Set D} (hs : s₀.Countable) (k : ℕ) :
    (reductionChain s₀ k : Set D).Countable := by
  induction k with
  | zero => exact countable_closure hs
  | succ k ih =>
    apply countable_closure
    refine ih.union ?_
    exact (ih.prod ih).biUnion fun p _ => Set.countable_range _

lemma witness_mem (s₀ : Set D) {k : ℕ} {a b : D} (ha : a ∈ reductionChain s₀ k)
    (hb : b ∈ reductionChain s₀ k) (i : Fin 5) :
    witness (a, b) i ∈ reductionChain s₀ (k + 1) := by
  apply Subring.subset_closure
  refine Or.inr (Set.mem_biUnion (x := (a, b)) ⟨ha, hb⟩ ⟨i, rfl⟩)

/-- **Proposition 6.5** (`prop:countable-reduction`). Let `D` be a Bézout domain and `F` a finite
matrix over `D` with no Smith normal form. There is a countable Bézout subdomain `S ⊂ D`
containing every entry of `F` over which `F` still has no Smith normal form. -/
theorem countable_reduction [IsDomain D] {m n : ℕ} (F : Matrix (Fin m) (Fin n) D)
    (hF : ¬ HasSmithNormalForm F) :
    ∃ S : Subring D, Countable S ∧ IsDomain S ∧ IsBezout S ∧
      ∃ F' : Matrix (Fin m) (Fin n) S, F'.map S.subtype = F ∧ ¬ HasSmithNormalForm F' := by
  set s₀ : Set D := Set.range fun ij : Fin m × Fin n => F ij.1 ij.2
  have hs₀ : s₀.Countable := Set.countable_range _
  set S : Subring D := ⨆ k, reductionChain s₀ k
  have hdir : Directed (· ≤ ·) (reductionChain s₀) := (reductionChain_mono s₀).directed_le
  have hmem : ∀ z, z ∈ S ↔ ∃ k, z ∈ reductionChain s₀ k := fun z =>
    Subring.mem_iSup_of_directed hdir
  have hle : ∀ k, reductionChain s₀ k ≤ S := fun k => le_iSup (reductionChain s₀) k
  refine ⟨S, ?_, inferInstance, ?_, ?_⟩
  · -- countability
    have : (S : Set D) = ⋃ k, (reductionChain s₀ k : Set D) :=
      Subring.coe_iSup_of_directed hdir
    have hc : (S : Set D).Countable := by
      rw [this]; exact Set.countable_iUnion fun k => reductionChain_countable hs₀ k
    exact hc.to_subtype
  · -- Bézout
    rw [IsBezout.iff_span_pair_isPrincipal]
    intro a b
    obtain ⟨k₁, hk₁⟩ := (hmem a).1 a.2
    obtain ⟨k₂, hk₂⟩ := (hmem b).1 b.2
    have ha : (a : D) ∈ reductionChain s₀ (max k₁ k₂) :=
      reductionChain_mono s₀ (le_max_left _ _) hk₁
    have hb : (b : D) ∈ reductionChain s₀ (max k₁ k₂) :=
      reductionChain_mono s₀ (le_max_right _ _) hk₂
    have hw : ∀ i, witness ((a : D), (b : D)) i ∈ S := fun i => hle _ (witness_mem s₀ ha hb i)
    let w : Fin 5 → S := fun i => ⟨witness ((a : D), (b : D)) i, hw i⟩
    obtain ⟨h0, h3, h4⟩ := witness_spec (a : D) (b : D)
    have e0 : w 0 = w 1 * a + w 2 * b := Subtype.ext h0
    have e3 : a = w 0 * w 3 := Subtype.ext h3
    have e4 : b = w 0 * w 4 := Subtype.ext h4
    refine ⟨⟨w 0, le_antisymm ?_ ?_⟩⟩
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · rw [e3]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      · rw [e4]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · show Ideal.span {w 0} ≤ Ideal.span {a, b}
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, e0]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · -- the matrix over `S`
    have hF0 : ∀ i j, F i j ∈ S := fun i j =>
      hle 0 (Subring.subset_closure ⟨(i, j), rfl⟩)
    refine ⟨fun i j => ⟨F i j, hF0 i j⟩, ?_, fun h => hF ?_⟩
    · ext i j; rfl
    · have := h.map S.subtype
      convert this
      ext i j; rfl

end CountableReduction

/-! ### Countable character and semihereditary rings -/

section CountableCharacter

variable (A : Type*) [CommRing A]

/-- A ring has *countable character* if every non-zero-divisor belongs to at most countably many
maximal ideals (for a domain: every nonzero element). -/
def HasCountableCharacter : Prop :=
  ∀ a ∈ nonZeroDivisors A, {m : Ideal A | m.IsMaximal ∧ a ∈ m}.Countable

/-- A ring is *semihereditary* if every finitely generated ideal is projective. -/
def IsSemihereditary : Prop := ∀ I : Ideal A, I.FG → Module.Projective A I

/-- A ring is an *elementary divisor ring* if every finite matrix has a Smith normal form. -/
def IsElementaryDivisorRing : Prop :=
  ∀ (m n : ℕ) (F : Matrix (Fin m) (Fin n) A), HasSmithNormalForm F

variable {A}

/-- Every Bézout domain is semihereditary: each nonzero finitely generated ideal is principal
and isomorphic to the ring. -/
theorem IsBezout.isSemihereditary [IsDomain A] [IsBezout A] : IsSemihereditary A := by
  intro I hI
  obtain ⟨g, hg⟩ := (IsBezout.isPrincipal_of_FG I hI).principal
  by_cases h0 : g = 0
  · have : I = ⊥ := by rw [hg, h0]; simp
    subst this
    exact Module.Projective.of_free
  · have e : A ≃ₗ[A] (Submodule.span A {g}) := LinearEquiv.toSpanNonzeroSingleton A A g h0
    rw [hg]
    exact Module.Projective.of_equiv e

lemma hasCountableCharacter_iff [IsDomain A] :
    HasCountableCharacter A ↔
      ∀ a : A, a ≠ 0 → {m : Ideal A | m.IsMaximal ∧ a ∈ m}.Countable := by
  simp only [HasCountableCharacter, mem_nonZeroDivisors_iff_ne_zero]

end CountableCharacter

/-! ### The countable domain `ℚ[t, z₁, z₂, …]` -/

section ExampleC

/-- `C = ℚ[t, z₁, z₂, …]`, with `t = X 0` and `z_{k+1} = X (k + 1)`. -/
abbrev ExampleC : Type := MvPolynomial ℕ ℚ

/-- `true ↦ 1`, `false ↦ 0`. -/
def boolToRat (b : Bool) : ℚ := if b then 1 else 0

lemma boolToRat_injective : Function.Injective boolToRat := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolToRat]

/-- The evaluation `t ↦ 0`, `z_{k+1} ↦ ε k` (for `ε ∈ {0,1}^ℕ`). -/
def evalε (ε : ℕ → Bool) : ExampleC →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval fun k => if k = 0 then 0 else boolToRat (ε (k - 1))

/-- The maximal ideal `𝔪_ε = (t, z₁ - ε₁, z₂ - ε₂, …)`. -/
def maxIdealε (ε : ℕ → Bool) : Ideal ExampleC := RingHom.ker (evalε ε)

lemma maxIdealε_isMaximal (ε : ℕ → Bool) : (maxIdealε ε).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun q => ⟨MvPolynomial.C q, by simp [evalε]⟩

lemma t_mem_maxIdealε (ε : ℕ → Bool) : (MvPolynomial.X 0 : ExampleC) ∈ maxIdealε ε := by
  simp [maxIdealε, evalε, RingHom.mem_ker]

lemma maxIdealε_injective : Function.Injective maxIdealε := by
  intro ε ε' h
  funext k
  have hmem : (MvPolynomial.X (k + 1) - MvPolynomial.C (boolToRat (ε k)) : ExampleC) ∈
      maxIdealε ε := by
    simp [maxIdealε, evalε, RingHom.mem_ker]
  rw [h] at hmem
  simp only [maxIdealε, evalε, RingHom.mem_ker, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at hmem
  have : boolToRat (ε' k) = boolToRat (ε k) := by
    have := sub_eq_zero.1 hmem
    simpa using this
  exact (boolToRat_injective this).symm

lemma not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
  apply Function.cantor_surjective (fun n => {k | f n k = true})
  intro s
  classical
  obtain ⟨n, hn⟩ := hf (fun k => decide (k ∈ s))
  exact ⟨n, by ext k; simp [hn]⟩

/-- `C` is countable. -/
lemma exampleC_countable : Countable ExampleC := inferInstance

/-- The nonzero element `t` of `C` lies in uncountably many maximal ideals. -/
theorem exampleC_uncountable :
    (MvPolynomial.X 0 : ExampleC) ≠ 0 ∧
      ¬ {m : Ideal ExampleC | m.IsMaximal ∧ MvPolynomial.X 0 ∈ m}.Countable := by
  refine ⟨MvPolynomial.X_ne_zero 0, fun hc => not_countable_nat_bool ?_⟩
  have hsub : Set.range maxIdealε ⊆ {m : Ideal ExampleC | m.IsMaximal ∧ MvPolynomial.X 0 ∈ m} := by
    rintro _ ⟨ε, rfl⟩
    exact ⟨maxIdealε_isMaximal ε, t_mem_maxIdealε ε⟩
  have := (hc.mono hsub).to_subtype
  exact Function.Injective.countable (f := fun ε => (⟨maxIdealε ε, ε, rfl⟩ : Set.range maxIdealε))
    fun a b hab => maxIdealε_injective (congrArg Subtype.val hab)

end ExampleC

end BezoutCounterexample
