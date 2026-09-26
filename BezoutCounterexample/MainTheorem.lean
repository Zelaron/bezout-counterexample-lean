import BezoutCounterexample.Construction
import BezoutCounterexample.Identities
import BezoutCounterexample.Principalization.RealPts

/-!
# Theorem 1.1 (`thm:main`)

Using Proposition 4.6 (`PrincipalizationExtension`, proved in
`BezoutCounterexample.Principalization.principalizationExtension` by weighted principalization),
the ring `R` of Construction 5.1 is a countable Bézout domain containing `A₀ = ℚ[x,y]` in which `Δ` is a nonzero nonunit and over
which the matrix `M` has no Smith normal form. Consequently `R` has characteristic zero and is
not an elementary divisor domain.

The proof follows the paper: a Smith normal form `U M V = diag(d₁, d₂)` forces `d₁` to be a unit
(because the entries of `M` generate the unit ideal); all the data then live in some `A_N`, and
evaluating at the points of `K_N` produces the nowhere vanishing section `z ↦ M(z) V(z) e₁` of
`L_N`, contradicting (5.2).
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology

variable (hPE : CoprimePairPE)

namespace R

/-- **Lemma 5.3** (`lem:key-obstruction`), the key obstruction: for no `p, q, u, v, e, c ∈ R` is
`e · (p, q) M (u, v)ᵀ = 1 + Δ c`.
(If it were, all these elements would come from some `A_N`, and at the points `z ∈ K_N`,
where `Δ` vanishes, `z ↦ M(z) (u(z), v(z))ᵀ` would be a nowhere vanishing section of `L_N`.) -/
theorem no_unit_value_mod (p q u v e c : R hPE) :
    e * (p * (1 + ι hPE x) * u + p * ι hPE y * v + q * ι hPE y * u + q * (1 - ι hPE x) * v)
      ≠ 1 + ι hPE Δ * c := by
  intro hrel
  obtain ⟨N, w, hw⟩ := exists_of_fin hPE 6 ![p, q, u, v, e, c]
  set S := stage hPE N
  set X : G hPE N := S.ι x
  set Y : G hPE N := S.ι y
  -- the relation already holds in `A_N`
  have hrelN : w 4 * (w 0 * (1 + X) * w 2 + w 0 * Y * w 3 + w 1 * Y * w 2 + w 1 * (1 - X) * w 3)
      = 1 + S.ι Δ * w 5 := by
    apply of_injective hPE N
    have hX : of hPE N X = ι hPE x := of_ι hPE N x
    have hY : of hPE N Y = ι hPE y := of_ι hPE N y
    have hΔ : of hPE N (S.ι Δ) = ι hPE Δ := of_ι hPE N Δ
    simp only [map_mul, map_add, map_sub, map_one, hX, hY, hΔ, hw]
    simpa using hrel
  -- the nowhere vanishing section `z ↦ M(z) (u(z), v(z))ᵀ` of `L_N`
  apply S.nonorientable
  refine ⟨fun z => (Mreal (z.1 X) (z.1 Y)).mulVec ![z.1 (w 2), z.1 (w 3)], ?_, fun z => ⟨?_, ?_⟩⟩
  · have hc : ∀ a : G hPE N, Continuous fun z : S.K => z.1 a :=
      fun a => (RealPt.continuous_eval a).comp continuous_subtype_val
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [Mreal_mulVec] <;> simp <;> fun_prop
  · intro h0
    have h := congrArg z.1 hrelN
    simp only [map_mul, map_add, map_sub, map_one, S.K_circle z.1 z.2, zero_mul,
      add_zero] at h
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp only [Mreal_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h1 h2
    have : z.1 (w 0) * ((1 + z.1 X) * z.1 (w 2) + z.1 Y * z.1 (w 3)) +
        z.1 (w 1) * (z.1 Y * z.1 (w 2) + (1 - z.1 X) * z.1 (w 3)) = 0 := by
      rw [h1, h2]; ring
    have h' : z.1 (w 4) * (z.1 (w 0) * ((1 + z.1 X) * z.1 (w 2) + z.1 Y * z.1 (w 3)) +
        z.1 (w 1) * (z.1 Y * z.1 (w 2) + (1 - z.1 X) * z.1 (w 3))) = 1 := by
      linear_combination h
    rw [this, mul_zero] at h'
    exact zero_ne_one h'
  · exact ⟨_, rfl⟩

/-- The key obstruction: for no `p, q, u, v, e ∈ R` is `e · (p, q) M (u, v)ᵀ = 1`. -/
theorem no_unit_value (p q u v e : R hPE) :
    e * (p * (1 + ι hPE x) * u + p * ι hPE y * v + q * ι hPE y * u + q * (1 - ι hPE x) * v)
      ≠ 1 := by
  have := no_unit_value_mod hPE p q u v e 0
  rwa [mul_zero, add_zero] at this

/-- **Theorem 1.1**: `M` has no Smith normal form over `R`. -/
theorem not_hasSmithNormalForm : ¬ HasSmithNormalForm (M.map (ι hPE)) := by
  intro hSNF
  have hgen : ∀ I : Ideal (R hPE), (∀ i j, (M.map (ι hPE)) i j ∈ I) → I = ⊤ := by
    intro I hI
    have h1 : ι hPE (1 + x) ∈ I := by simpa [M] using hI 0 0
    have h2 : ι hPE (1 - x) ∈ I := by simpa [M] using hI 1 1
    have h3 : ι hPE (1 + x) + ι hPE (1 - x) = ι hPE (MvPolynomial.C 2) := by
      rw [← map_add]; congr 1; rw [map_ofNat]; ring
    have h4 : ι hPE (MvPolynomial.C 2) * ι hPE (MvPolynomial.C (1 / 2)) = 1 := by
      rw [← map_mul, ← map_mul]; norm_num
    rw [Ideal.eq_top_iff_one, ← h4, ← h3]
    exact Ideal.mul_mem_right _ _ (Ideal.add_mem _ h1 h2)
  obtain ⟨p, q, u, v, e, h⟩ := exists_of_hasSmithNormalForm _ hgen hSNF
  apply no_unit_value hPE p q u v e
  simpa [M] using h

/-- **Theorem 1.1**: `R` is not an elementary divisor domain. -/
theorem not_isElementaryDivisorDomain : ¬ IsElementaryDivisorDomain (R hPE) :=
  fun h => not_hasSmithNormalForm hPE (h.2 2 2 _)

end R

/-- **Theorem 1.1** (`thm:main`), assuming Proposition 4.6 for coprime pairs (`CoprimePairPE`).

There is a countable Bézout domain `R` containing `A₀ = ℚ[x,y]` (i.e. with an injective ring
homomorphism `ι : A₀ → R`; equivalently `x` and `y` stay algebraically independent over `ℚ`)
such that `Δ` is a nonzero nonunit of `R` and `M` has no Smith normal form over `R`.
Consequently, `R` has characteristic zero and is not an elementary divisor domain. -/
theorem main_theorem_of_coprimePair (hPE : CoprimePairPE) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ι : A₀ →+* R),
      Countable R ∧ IsBezout R ∧ Function.Injective ι ∧ ι Δ ≠ 0 ∧ ¬ IsUnit (ι Δ) ∧
      ¬ HasSmithNormalForm (M.map ι) ∧ CharZero R ∧ ¬ IsElementaryDivisorDomain R :=
  ⟨R hPE, inferInstance, inferInstance, R.ι hPE, inferInstance, inferInstance,
    R.ι_injective hPE, R.Δ_ne_zero hPE, R.Δ_not_isUnit hPE, R.not_hasSmithNormalForm hPE,
    inferInstance, R.not_isElementaryDivisorDomain hPE⟩

/-- **Theorem 1.1** (`thm:main`), from Proposition 4.6 (`PrincipalizationExtension`). -/
theorem main_theorem_of_principalization (hPE : PrincipalizationExtension) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ι : A₀ →+* R),
      Countable R ∧ IsBezout R ∧ Function.Injective ι ∧ ι Δ ≠ 0 ∧ ¬ IsUnit (ι Δ) ∧
      ¬ HasSmithNormalForm (M.map ι) ∧ CharZero R ∧ ¬ IsElementaryDivisorDomain R :=
  main_theorem_of_coprimePair hPE.coprimePair

/-- Proposition 4.6 for coprime pairs holds. -/
theorem coprimePairPE_holds : CoprimePairPE :=
  Principalization.principalizationExtension.coprimePair

/-- **Theorem 1.1** (`thm:main`), unconditionally.

There is a countable Bézout domain `R` containing `A₀ = ℚ[x,y]` (i.e. with an injective ring
homomorphism `ι : A₀ → R`) such that `Δ` is a nonzero nonunit of `R` and `M` has no Smith normal
form over `R`. Consequently, `R` has characteristic zero and is not an elementary divisor
domain. -/
theorem main_theorem :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ι : A₀ →+* R),
      Countable R ∧ IsBezout R ∧ Function.Injective ι ∧ ι Δ ≠ 0 ∧ ¬ IsUnit (ι Δ) ∧
      ¬ HasSmithNormalForm (M.map ι) ∧ CharZero R ∧ ¬ IsElementaryDivisorDomain R :=
  main_theorem_of_principalization Principalization.principalizationExtension

end BezoutCounterexample
