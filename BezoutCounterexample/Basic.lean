import Mathlib

/-!
# Section 1: definitions and the initial data

This file contains the notions of Section 1 of

  C. Hägg, A. Mörtberg, *A Bézout domain that is not an elementary divisor domain*,

and the initial data (1.1).

Throughout, rings are commutative with identity and ring homomorphisms preserve the identity
(`CommRing`, `RingHom`).

* A *Bézout domain* is an integral domain in which every finitely generated ideal is principal
  (`IsDomain R ∧ IsBezout R`); equivalently, every two-generated ideal is principal
  (`isBezout_iff_span_pair_isPrincipal`).
* `MatrixEquivalent F G`: `P F Q = G` for some `P ∈ GL_m(A)`, `Q ∈ GL_n(A)`.
* `IsSmithNormalForm D`: `D` is diagonal, its nonzero diagonal entries occur first and satisfy
  `d₁ ∣ d₂ ∣ ⋯ ∣ d_r`. `HasSmithNormalForm F`: `F` is equivalent to such a matrix.
* `IsElementaryDivisorDomain R`: a domain over which every finite matrix has a Smith normal form.
  Every elementary divisor domain is Bézout (`IsElementaryDivisorDomain.isBezout`), by applying
  the definition to `1 × 2` matrices.
* (1.1): `A₀ = ℚ[x, y]`, `Δ = x² + y² - 1`, `M = [[1 + x, y], [y, 1 - x]]`, where `x` and `y`
  are algebraically independent over `ℚ` (`algebraicIndependent_x_y`).

Lean indices start at `0`, so the diagonal entries `d₁, d₂, …` of the paper are `d 0, d 1, …`.
-/

noncomputable section

namespace BezoutCounterexample

open MvPolynomial

/-! ## Bézout domains -/

/-- A domain is Bézout (every finitely generated ideal is principal) if and only if every
two-generated ideal is principal. -/
theorem isBezout_iff_span_pair_isPrincipal (R : Type*) [CommRing R] :
    IsBezout R ↔ ∀ a b : R, (Ideal.span {a, b} : Ideal R).IsPrincipal :=
  IsBezout.iff_span_pair_isPrincipal

/-! ## Equivalence of matrices, Smith normal form and elementary divisor domains -/

section SNF

variable {R : Type*} [CommRing R]

/-- Two `m × n` matrices `F` and `G` are *equivalent* if `P F Q = G` for some
`P ∈ GL_m(R)` and `Q ∈ GL_n(R)`. -/
def MatrixEquivalent {m n : ℕ} (F G : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (P : GL (Fin m) R) (Q : GL (Fin n) R),
    (P : Matrix (Fin m) (Fin m) R) * F * (Q : Matrix (Fin n) (Fin n) R) = G

/-- A matrix `D` is in *Smith normal form* if it is diagonal (with diagonal entries `d 0, d 1, …`),
its nonzero diagonal entries occur first (they are `d 0, …, d (r-1)`), and these satisfy
`d 0 ∣ d 1 ∣ ⋯ ∣ d (r-1)`. -/
def IsSmithNormalForm {m n : ℕ} (D : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (d : ℕ → R) (r : ℕ), r ≤ min m n ∧
    (∀ i j, D i j = if (i : ℕ) = j then d i else 0) ∧
    (∀ k < min m n, d k ≠ 0 ↔ k < r) ∧
    ∀ k, k + 1 < r → d k ∣ d (k + 1)

/-- A *Smith normal form* of `F` is an equivalent matrix in Smith normal form. -/
def HasSmithNormalForm {m n : ℕ} (F : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ G, MatrixEquivalent F G ∧ IsSmithNormalForm G

variable (R) in
/-- A domain is an *elementary divisor domain* if every finite matrix over it has a Smith normal
form. -/
def IsElementaryDivisorDomain : Prop :=
  IsDomain R ∧ ∀ (m n : ℕ) (F : Matrix (Fin m) (Fin n) R), HasSmithNormalForm F

/-- Smith normal form as a divisibility chain: since `0 ∣ a` forces `a = 0`, a diagonal matrix is
in Smith normal form if and only if its diagonal entries satisfy `d k ∣ d (k + 1)` for all `k`. -/
theorem isSmithNormalForm_iff_chain {m n : ℕ} (D : Matrix (Fin m) (Fin n) R) :
    IsSmithNormalForm D ↔ ∃ d : ℕ → R, (∀ i j, D i j = if (i : ℕ) = j then d i else 0) ∧
      ∀ k, k + 1 < min m n → d k ∣ d (k + 1) := by
  constructor
  · rintro ⟨d, r, hr, hD, hnz, hdiv⟩
    refine ⟨d, hD, fun k hk => ?_⟩
    by_cases hkr : k + 1 < r
    · exact hdiv k hkr
    · have : d (k + 1) = 0 := by
        by_contra h
        exact hkr ((hnz (k + 1) hk).1 h)
      rw [this]
      exact dvd_zero _
  · classical
    rintro ⟨d, hD, hdiv⟩
    -- the number of leading nonzero diagonal entries
    let P : ℕ → Prop := fun k => k < min m n → d k = 0
    have hP : ∃ k, P k := ⟨min m n, fun h => absurd h (lt_irrefl _)⟩
    let r := Nat.find hP
    have hr : r ≤ min m n := Nat.find_min' hP (fun h => absurd h (lt_irrefl _))
    have hlt : ∀ k < r, d k ≠ 0 := by
      intro k hk h0
      exact Nat.find_min hP hk (fun _ => h0)
    have hzero : ∀ k, r ≤ k → k < min m n → d k = 0 := by
      intro k hrk hk
      induction k, hrk using Nat.le_induction with
      | base => exact Nat.find_spec hP hk
      | succ k hrk ih =>
        have h0 : d k = 0 := ih (by omega)
        have := hdiv k hk
        rw [h0, zero_dvd_iff] at this
        exact this
    refine ⟨d, r, hr, hD, fun k hk => ⟨fun h => ?_, fun h => hlt k h⟩, fun k hk => hdiv k ?_⟩
    · by_contra hkr
      exact h (hzero k (not_lt.1 hkr) hk)
    · omega

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

/-- Multiplication by invertible matrices on either side preserves the ideal generated by all
matrix entries: if `F` and `G` are equivalent and the entries of `G` lie in an ideal `I`, then
so do the entries of `F`. -/
lemma MatrixEquivalent.entry_mem {m n : ℕ} {F G : Matrix (Fin m) (Fin n) R}
    (h : MatrixEquivalent F G) (I : Ideal R) (hG : ∀ i j, G i j ∈ I) (i : Fin m) (j : Fin n) :
    F i j ∈ I := by
  obtain ⟨P, Q, hPQ⟩ := h
  rw [eq_inv_mul_mul hPQ]
  exact entry_mem_of_mul _ G _ I hG i j

/-- **Every elementary divisor domain is a Bézout domain**: apply the definition to `1 × 2`
matrices. -/
theorem IsElementaryDivisorDomain.isBezout (h : IsElementaryDivisorDomain R) : IsBezout R := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  obtain ⟨G, hFG, hG⟩ := h.2 1 2 !![a, b]
  obtain ⟨d, hD, -⟩ := (isSmithNormalForm_iff_chain G).1 hG
  have hGd : ∀ i j, G i j ∈ (Ideal.span {d 0} : Ideal R) := by
    intro i j
    fin_cases i; fin_cases j
    · rw [hD]; exact Ideal.subset_span rfl
    · rw [hD]; simp
  refine ⟨⟨d 0, le_antisymm ?_ ?_⟩⟩
  · rw [Ideal.span_le]
    intro r hr
    rcases hr with rfl | rfl
    · simpa using hFG.entry_mem _ hGd 0 0
    · simpa using hFG.entry_mem _ hGd 0 1
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    obtain ⟨P, Q, hPQ⟩ := hFG
    have h00 : d 0 = G 0 0 := by rw [hD 0 0]; simp
    rw [h00, ← hPQ]
    refine entry_mem_of_mul _ _ _ _ (fun i j => ?_) 0 0
    fin_cases i; fin_cases j
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)

end SNF

/-! ## The initial data (1.1) -/

/-- `A₀ = ℚ[x, y]`. -/
abbrev A₀ : Type := MvPolynomial (Fin 2) ℚ

/-- The variable `x`. -/
def x : A₀ := X 0

/-- The variable `y`. -/
def y : A₀ := X 1

/-- `Δ = x² + y² - 1`. -/
def Δ : A₀ := x ^ 2 + y ^ 2 - 1

/-- `M = [[1 + x, y], [y, 1 - x]]`. -/
def M : Matrix (Fin 2) (Fin 2) A₀ := !![1 + x, y; y, 1 - x]

/-- `x` and `y` are algebraically independent over `ℚ`. -/
theorem algebraicIndependent_x_y : AlgebraicIndependent ℚ ![x, y] := by
  have h := MvPolynomial.algebraicIndependent_X (Fin 2) ℚ
  convert h using 1
  funext i
  fin_cases i <;> rfl

end BezoutCounterexample
