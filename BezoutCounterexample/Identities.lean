import BezoutCounterexample.Defs

/-!
# Elementary algebraic facts

* The identities (2.1): `det M = -Δ`, `(1+x, y, 1-x) = A₀`, `M² - 2M = Δ I₂`.
* On the circle, `½ M` is an idempotent of rank one (`Mreal_half_idempotent`, `Mreal_det`,
  `Mreal_trace`).
* Every elementary divisor domain is Bézout (Section 1: apply the definition to `1 × 2`
  matrices).
* `isUnit_of_hasSmithNormalForm`: if the entries of a `2 × 2` matrix `F` generate the unit ideal
  and `F` has a Smith normal form `P F Q = diag(d₁, d₂)`, then `d₁` is a unit; this is the first
  step of the proof of Theorem 1.1.
-/

noncomputable section

namespace BezoutCounterexample

open Matrix

/-! ### The identities (2.1) -/

theorem det_M : M.det = -Δ := by
  simp [M, Δ, Matrix.det_fin_two]
  ring

theorem span_entries_M : (Ideal.span {1 + x, y, 1 - x} : Ideal A₀) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h2 : MvPolynomial.C (1 / 2 : ℚ) * (1 + x) + MvPolynomial.C (1 / 2 : ℚ) * (1 - x) =
      (1 : A₀) := by
    rw [← mul_add]
    have : (1 + x) + (1 - x) = (MvPolynomial.C (2 : ℚ) : A₀) := by
      rw [map_ofNat]; ring
    rw [this, ← map_mul]
    norm_num
  have hmem : MvPolynomial.C (1 / 2 : ℚ) * (1 + x) + MvPolynomial.C (1 / 2 : ℚ) * (1 - x) ∈
      (Ideal.span {1 + x, y, 1 - x} : Ideal A₀) :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  rwa [h2] at hmem

theorem M_sq : M * M - (2 : A₀) • M = Δ • (1 : Matrix (Fin 2) (Fin 2) A₀) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [M, Δ] <;> ring

/-- Evaluating `M` at a real point. -/
theorem M_map (A : Type*) [CommRing A] (ι : A₀ →+* A) (z : A →+* ℝ) :
    (M.map ι).map z = Mreal (z (ι x)) (z (ι y)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Mreal]

theorem Mreal_det (a b : ℝ) : (Mreal a b).det = 1 - a ^ 2 - b ^ 2 := by
  simp [Mreal, Matrix.det_fin_two]; ring

theorem Mreal_trace (a b : ℝ) : (Mreal a b).trace = 2 := by
  simp [Mreal, Matrix.trace_fin_two]; ring

/-- On the circle, `½ M` is idempotent. -/
theorem Mreal_half_idempotent {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    ((1 / 2 : ℝ) • Mreal a b) * ((1 / 2 : ℝ) • Mreal a b) = (1 / 2 : ℝ) • Mreal a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mreal, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hab]

lemma rank_pos_of_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (h : A ≠ 0) : 0 < A.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h0
  simpa [Matrix.mulVec_single] using this

/-- On the circle, `½ M` has rank one. -/
theorem Mreal_rank {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) : ((1 / 2 : ℝ) • Mreal a b).rank = 1 := by
  set P := (1 / 2 : ℝ) • Mreal a b with hPdef
  have hP : P * P = P := Mreal_half_idempotent hab
  have h1 : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero h1
  have htr : P.trace = 1 := by
    rw [hPdef, Matrix.trace_smul, Mreal_trace, smul_eq_mul]; norm_num
  have hP0 : P ≠ 0 := by
    intro h; rw [h, Matrix.trace_zero] at htr; exact zero_ne_one htr
  have hQ0 : (1 - P) ≠ 0 := by
    intro h
    have := congrArg Matrix.trace h
    rw [Matrix.trace_sub, htr, Matrix.trace_one, Matrix.trace_zero] at this
    norm_num at this
  have r1 := rank_pos_of_ne_zero hP0
  have r2 := rank_pos_of_ne_zero hQ0
  simp only [Fintype.card_fin] at hsum
  omega

/-! ### Smith normal forms -/

section SNF

variable {R : Type*} [CommRing R]

/-- Entries of `A * G * B` lie in any ideal containing the entries of `G`. -/
lemma entry_mem_of_mul {m n k l : Type*} [Fintype k] [Fintype l] (A : Matrix m k R)
    (G : Matrix k l R) (B : Matrix l n R) (I : Ideal R) (hG : ∀ i j, G i j ∈ I) (i : m) (j : n) :
    (A * G * B) i j ∈ I := by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hG k l))

/-- If `P F Q = G` with `P, Q` invertible then `F = P⁻¹ G Q⁻¹`. -/
lemma eq_inv_mul_mul {m n : ℕ} {F G : Matrix (Fin m) (Fin n) R} {P : GL (Fin m) R}
    {Q : GL (Fin n) R}
    (h : (P : Matrix (Fin m) (Fin m) R) * F * (Q : Matrix (Fin n) (Fin n) R) = G) :
    F = ((P⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * G *
      ((Q⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
  rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- Every elementary divisor domain is a Bézout domain (apply the definition to `1 × 2`
matrices). -/
theorem IsElementaryDivisorDomain.isBezout (h : IsElementaryDivisorDomain R) : IsBezout R := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  obtain ⟨G, ⟨P, Q, hPQ⟩, d, hd, -⟩ := h.2 1 2 !![a, b]
  have hG : ∀ i j, G i j ∈ (Ideal.span {d 0} : Ideal R) := by
    intro i j
    fin_cases i; fin_cases j
    · rw [hd]; exact Ideal.subset_span rfl
    · rw [hd]; simp
  refine ⟨⟨d 0, le_antisymm ?_ ?_⟩⟩
  · have hF := eq_inv_mul_mul hPQ
    rw [Ideal.span_le]
    intro r hr
    rcases hr with rfl | rfl
    · have := entry_mem_of_mul ((P⁻¹ : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) G
        ((Q⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) _ hG 0 0
      rw [← hF] at this
      simpa using this
    · have := entry_mem_of_mul ((P⁻¹ : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R) G
        ((Q⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) _ hG 0 1
      rw [← hF] at this
      simpa using this
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h00 : d 0 = G 0 0 := by rw [hd 0 0]; simp
    rw [h00, ← hPQ]
    refine entry_mem_of_mul _ _ _ _ (fun i j => ?_) 0 0
    fin_cases i; fin_cases j
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)

/-- If the entries of a `2 × 2` matrix `F` generate the unit ideal and `P F Q` is in Smith normal
form, then the first diagonal entry of `P F Q` is a unit. Consequently there are
`p q u v e` with `e · (p, q) F (u, v)ᵀ = 1`. -/
theorem exists_of_hasSmithNormalForm (F : Matrix (Fin 2) (Fin 2) R)
    (hF : ∀ I : Ideal R, (∀ i j, F i j ∈ I) → I = ⊤) (h : HasSmithNormalForm F) :
    ∃ p q u v e : R,
      e * (p * F 0 0 * u + p * F 0 1 * v + q * F 1 0 * u + q * F 1 1 * v) = 1 := by
  obtain ⟨G, ⟨P, Q, hPQ⟩, d, hd, hdiv⟩ := h
  have hG00 : G 0 0 = d 0 := by rw [hd]; simp
  obtain ⟨c, hc⟩ := hdiv 0 (by norm_num)
  simp only [zero_add] at hc
  have hG : ∀ i j, G i j ∈ (Ideal.span {d 0} : Ideal R) := by
    intro i j
    fin_cases i <;> fin_cases j <;> rw [hd] <;> simp [hc, Ideal.mem_span_singleton]
  have hmem : ∀ i j, F i j ∈ Ideal.span {d 0} := by
    intro i j
    rw [eq_inv_mul_mul hPQ]
    exact entry_mem_of_mul _ G _ _ hG i j
  have htop := hF _ hmem
  rw [Ideal.span_singleton_eq_top] at htop
  obtain ⟨e, he⟩ := htop.exists_left_inv
  refine ⟨P 0 0, P 0 1, Q 0 0, Q 1 0, e, ?_⟩
  rw [← he, ← hG00, ← hPQ]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

end SNF

end BezoutCounterexample
