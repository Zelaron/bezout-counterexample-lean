import BezoutCounterexample.Consequences

/-!
# Couchot's theorem for `2 × 2` matrices, and Corollary 6.4

Couchot [Couchot, Theorem 12] proved that every semihereditary Bézout ring of countable
character is an elementary divisor ring; for domains this is Fuchs–Salce, *Modules over
non-Noetherian domains*, Theorem III.6.5. Corollary 6.4 of the paper only needs the case of
`2 × 2` matrices over a Bézout domain, which is proved here following Chen–Sheibani
(*Elementary matrix reduction over Bézout duo-domains*, Lemma 5.1):

* `MatrixEquivalent.refl/symm/trans`, `HasSmithNormalForm.of_equiv`, `.of_transpose`, `.smul`;
* `exists_bezout_data`, `gl2`: Hermite reductions of pairs in a Bézout domain;
* `reduction_step`: starting from `[[a, 0], [b, c]]` with `(a, b, c) = 1`, the corner can be
  replaced (up to equivalence and transposition) by one generating a larger ideal and avoiding a
  given maximal ideal;
* `lower_hasSNF`: iterating along an enumeration `M₁, M₂, …` of the maximal ideals containing
  `a`, the union of the corner ideals is not proper (a maximal ideal containing it would be some
  `Mₖ`, which the `k`-th corner avoids), so some corner is a unit;
* `hasSNF_two_of_countableCharacter`: **every `2 × 2` matrix over a Bézout domain of countable
  character has a Smith normal form**;
* `R.not_hasCountableCharacter`, `corollary_6_4`: **Corollary 6.4**, unconditionally;
* `not_countable_row_of_not_hasSNF`, `R.not_countable_maximal`: an explicit form: uncountably many
  maximal ideals of `R` contain `(1 + x, y)`, and uncountably many contain `(1 - x, y)`.
-/

noncomputable section

namespace BezoutCounterexample

open Matrix

section Equiv

variable {R : Type*} [CommRing R] {m n : ℕ}

lemma MatrixEquivalent.refl (F : Matrix (Fin m) (Fin n) R) : MatrixEquivalent F F :=
  ⟨1, 1, by simp⟩

lemma MatrixEquivalent.symm {F G : Matrix (Fin m) (Fin n) R} (h : MatrixEquivalent F G) :
    MatrixEquivalent G F := by
  obtain ⟨P, Q, rfl⟩ := h
  refine ⟨P⁻¹, Q⁻¹, ?_⟩
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

lemma MatrixEquivalent.trans {F G H : Matrix (Fin m) (Fin n) R} (h1 : MatrixEquivalent F G)
    (h2 : MatrixEquivalent G H) : MatrixEquivalent F H := by
  obtain ⟨P, Q, rfl⟩ := h1
  obtain ⟨P', Q', rfl⟩ := h2
  refine ⟨P' * P, Q * Q', ?_⟩
  simp only [Units.val_mul, Matrix.mul_assoc]

lemma MatrixEquivalent.mul_left {F : Matrix (Fin m) (Fin n) R} (P : GL (Fin m) R) :
    MatrixEquivalent F ((P : Matrix (Fin m) (Fin m) R) * F) :=
  ⟨P, 1, by simp⟩

lemma MatrixEquivalent.mul_right {F : Matrix (Fin m) (Fin n) R} (Q : GL (Fin n) R) :
    MatrixEquivalent F (F * (Q : Matrix (Fin n) (Fin n) R)) :=
  ⟨1, Q, by simp⟩

lemma HasSmithNormalForm.of_equiv {F G : Matrix (Fin m) (Fin n) R} (h : MatrixEquivalent F G)
    (hG : HasSmithNormalForm G) : HasSmithNormalForm F := by
  obtain ⟨H, hGH, hH⟩ := hG
  exact ⟨H, h.trans hGH, hH⟩

/-- The transpose of an invertible matrix. -/
def glTranspose (P : GL (Fin n) R) : GL (Fin n) R :=
  ⟨(P : Matrix (Fin n) (Fin n) R)ᵀ, ((P⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ, by
    rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one], by
    rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]⟩

lemma IsSmithNormalForm.transpose {D : Matrix (Fin m) (Fin n) R} (h : IsSmithNormalForm D) :
    IsSmithNormalForm Dᵀ := by
  obtain ⟨d, hd, hdiv⟩ := h
  refine ⟨d, fun i j => ?_, fun k hk => hdiv k (by rw [min_comm]; exact hk)⟩
  rw [transpose_apply, hd]
  by_cases h : (j : ℕ) = (i : ℕ)
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma HasSmithNormalForm.of_transpose {F : Matrix (Fin m) (Fin n) R}
    (h : HasSmithNormalForm Fᵀ) : HasSmithNormalForm F := by
  obtain ⟨G, ⟨P, Q, hPQ⟩, hG⟩ := h
  refine ⟨Gᵀ, ⟨glTranspose Q, glTranspose P, ?_⟩, hG.transpose⟩
  rw [← hPQ]
  simp only [glTranspose, Units.val_mk, transpose_mul, transpose_transpose, Matrix.mul_assoc]

/-- All entries lie in no proper ideal. -/
def Unimod (A : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ I : Ideal R, (∀ i j, A i j ∈ I) → I = ⊤

lemma entries_mem_mul {I : Ideal R} {k l : ℕ} {X : Matrix (Fin m) (Fin n) R}
    (hX : ∀ i j, X i j ∈ I) (Y : Matrix (Fin k) (Fin m) R) (Z : Matrix (Fin n) (Fin l) R) :
    ∀ i j, (Y * X * Z) i j ∈ I := by
  intro i j
  simp only [mul_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hX b a))

lemma Unimod.equiv {A B : Matrix (Fin m) (Fin n) R} (hA : Unimod A) (h : MatrixEquivalent A B) :
    Unimod B := by
  obtain ⟨P, Q, rfl⟩ := h
  intro I hI
  apply hA I
  have := entries_mem_mul hI ((P⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)
    ((Q⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  intro i j
  have h2 := this i j
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at h2

lemma Unimod.transpose {A : Matrix (Fin m) (Fin n) R} (hA : Unimod A) : Unimod Aᵀ :=
  fun I hI => hA I fun i j => hI j i

end Equiv

end BezoutCounterexample

namespace BezoutCounterexample

open Matrix

section Bezout2

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]

/-- **Bézout data**: `a = a' g`, `b = b' g`, `r a' + s b' = 1` (so `g = r a + s b` is a gcd). -/
lemma exists_bezout_data (a b : R) :
    ∃ r s a' b' g : R, a = a' * g ∧ b = b' * g ∧ r * a' + s * b' = 1 := by
  obtain ⟨g, hg⟩ := (IsBezout.iff_span_pair_isPrincipal.1 inferInstance a b).principal
  by_cases h0 : g = 0
  · have ha : a ∈ Ideal.span {a, b} := Ideal.subset_span (by simp)
    have hb : b ∈ Ideal.span {a, b} := Ideal.subset_span (by simp)
    rw [hg, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at ha hb
    exact ⟨1, 0, 1, 0, 0, by simp [ha], by simp [hb], by ring⟩
  · have hgmem : g ∈ Ideal.span {a, b} := by rw [hg]; exact Submodule.mem_span_singleton_self g
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 hgmem
    have ha : a ∈ R ∙ g := by rw [← hg]; exact Ideal.subset_span (by simp)
    have hb : b ∈ R ∙ g := by rw [← hg]; exact Ideal.subset_span (by simp)
    obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.1 ha
    obtain ⟨b', hb'⟩ := Submodule.mem_span_singleton.1 hb
    rw [smul_eq_mul] at ha' hb'
    refine ⟨r, s, a', b', g, ha'.symm, hb'.symm, ?_⟩
    have : (r * a' + s * b') * g = 1 * g := by
      rw [one_mul, add_mul, mul_assoc, mul_assoc, ha', hb', hrs]
    exact mul_right_cancel₀ h0 this

variable (R) in
/-- The invertible matrix `[[r, s], [-b', a']]` of Bézout data. -/
def gl2 (r s a' b' : R) (h : r * a' + s * b' = 1) : GL (Fin 2) R :=
  ⟨!![r, s; -b', a'], !![a', -s; b', r], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | linear_combination -h | ring, by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | linear_combination -h | ring⟩

@[simp] lemma gl2_val (r s a' b' : R) (h : r * a' + s * b' = 1) :
    ((gl2 R r s a' b' h : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![r, s; -b', a'] := rfl

variable (R) in
/-- The column operation "add column 1 to column 0". -/
def glAddCol : GL (Fin 2) R :=
  ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- A lower triangular matrix with a unit in the corner has a Smith normal form. -/
lemma hasSNF_of_unit_corner (A : Matrix (Fin 2) (Fin 2) R) (hA : A 0 1 = 0)
    (hu : IsUnit (A 0 0)) : HasSmithNormalForm A := by
  obtain ⟨u, hu⟩ := hu
  set P : GL (Fin 2) R := ⟨!![(u⁻¹ : Rˣ), 0; -(A 1 0) * (u⁻¹ : Rˣ), 1], !![(u : R), 0; A 1 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  refine ⟨!![1, 0; 0, A 1 1], ⟨P, 1, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hA, ← hu]
  · refine ⟨fun k => if k = 0 then 1 else A 1 1, fun i j => ?_, fun k hk => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp
    · have hk0 : k = 0 := by simp at hk; omega
      subst hk0
      simp

end Bezout2

end BezoutCounterexample

namespace BezoutCounterexample

open Matrix

section Step

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]

/-- **The reduction step** (Chen–Sheibani, Lemma 5.1; Fuchs–Salce III.6.5): from a lower
triangular unimodular matrix, produce another one (up to equivalence and transposition) whose
corner generates a larger ideal and avoids the given maximal ideal. -/
lemma reduction_step (A : Matrix (Fin 2) (Fin 2) R) (hA : A 0 1 = 0) (hu : Unimod A)
    (M : Ideal R) (hM : M.IsMaximal) :
    ∃ B : Matrix (Fin 2) (Fin 2) R, (HasSmithNormalForm B → HasSmithNormalForm A) ∧
      B 0 1 = 0 ∧ Unimod B ∧ B 0 0 ∉ M ∧ Ideal.span {A 0 0} ≤ Ideal.span {B 0 0} := by
  classical
  -- first make the entry below the corner avoid `M` when needed
  obtain ⟨A₁, hAA₁, h00, h01, h10mem, h11⟩ : ∃ A₁ : Matrix (Fin 2) (Fin 2) R,
      MatrixEquivalent A A₁ ∧ A₁ 0 0 = A 0 0 ∧ A₁ 0 1 = 0 ∧
      (A 0 0 ∈ M → A₁ 1 0 ∉ M) ∧ A₁ 1 1 = A 1 1 := by
    by_cases hb : A 1 0 ∈ M
    · refine ⟨A * (glAddCol R : Matrix (Fin 2) (Fin 2) R), MatrixEquivalent.mul_right _, ?_, ?_,
        fun ha h => ?_, ?_⟩
      · simp [glAddCol, Matrix.mul_apply, Fin.sum_univ_two, hA]
      · simp [glAddCol, Matrix.mul_apply, Fin.sum_univ_two, hA]
      · have hc : A 1 1 ∈ M := by
          have : (A * (glAddCol R : Matrix (Fin 2) (Fin 2) R)) 1 0 = A 1 0 + A 1 1 := by
            simp [glAddCol, Matrix.mul_apply, Fin.sum_univ_two]
          rw [this] at h
          have := M.sub_mem h hb
          rwa [add_sub_cancel_left] at this
        apply hM.ne_top
        apply hu M
        intro i j
        fin_cases i <;> fin_cases j
        · exact ha
        · simp only [Fin.zero_eta, Fin.mk_one]; rw [hA]; exact M.zero_mem
        · exact hb
        · exact hc
      · simp [glAddCol, Matrix.mul_apply, Fin.sum_univ_two]
    · exact ⟨A, MatrixEquivalent.refl A, rfl, hA, fun _ => hb, rfl⟩
  -- the Hermite reduction of the first column
  obtain ⟨r, s, a', b', g, ha, hb, hrs⟩ := exists_bezout_data (A₁ 0 0) (A₁ 1 0)
  set U := ((gl2 R r s a' b' hrs : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * A₁ with hU
  have hU00 : U 0 0 = g := by
    simp only [hU, gl2_val, Matrix.mul_apply, Fin.sum_univ_two]
    simp; rw [ha, hb]; linear_combination g * hrs
  have hU10 : U 1 0 = 0 := by
    simp only [hU, gl2_val, Matrix.mul_apply, Fin.sum_univ_two]
    simp; rw [ha, hb]; ring
  refine ⟨Uᵀ, fun h => ?_, ?_, ?_, ?_, ?_⟩
  · exact HasSmithNormalForm.of_equiv hAA₁
      (HasSmithNormalForm.of_equiv (MatrixEquivalent.mul_left _) h.of_transpose)
  · rw [transpose_apply]; exact hU10
  · exact ((hu.equiv hAA₁).equiv (MatrixEquivalent.mul_left _)).transpose
  · rw [transpose_apply, hU00]
    intro hg
    by_cases ha0 : A 0 0 ∈ M
    · apply h10mem ha0
      rw [hb]; exact M.mul_mem_left _ hg
    · apply ha0
      rw [← h00, ha]; exact M.mul_mem_left _ hg
  · rw [transpose_apply, hU00, Ideal.span_singleton_le_span_singleton, ← h00, ha]
    exact dvd_mul_left g a'

end Step

end BezoutCounterexample

namespace BezoutCounterexample

open Matrix

section Iter

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]

/-- Lower triangular unimodular `2 × 2` matrices. -/
abbrev LowerUni (R : Type*) [CommRing R] :=
  {B : Matrix (Fin 2) (Fin 2) R // B 0 1 = 0 ∧ Unimod B}

/-- One reduction step, chosen. -/
def stepLU (B : LowerUni R) (M : Ideal R) (hM : M.IsMaximal) : LowerUni R :=
  ⟨Classical.choose (reduction_step B.1 B.2.1 B.2.2 M hM),
    (Classical.choose_spec (reduction_step B.1 B.2.1 B.2.2 M hM)).2.1,
    (Classical.choose_spec (reduction_step B.1 B.2.1 B.2.2 M hM)).2.2.1⟩

lemma stepLU_spec (B : LowerUni R) (M : Ideal R) (hM : M.IsMaximal) :
    (HasSmithNormalForm (stepLU B M hM).1 → HasSmithNormalForm B.1) ∧
      (stepLU B M hM).1 0 0 ∉ M ∧ Ideal.span {B.1 0 0} ≤ Ideal.span {(stepLU B M hM).1 0 0} :=
  ⟨(Classical.choose_spec (reduction_step B.1 B.2.1 B.2.2 M hM)).1,
    (Classical.choose_spec (reduction_step B.1 B.2.1 B.2.2 M hM)).2.2.2.1,
    (Classical.choose_spec (reduction_step B.1 B.2.1 B.2.2 M hM)).2.2.2.2⟩

/-- The sequence of reductions along an enumeration of maximal ideals. -/
def seqLU (B₀ : LowerUni R) (f : ℕ → Ideal R) (hf : ∀ k, (f k).IsMaximal) : ℕ → LowerUni R
  | 0 => B₀
  | k + 1 => stepLU (seqLU B₀ f hf k) (f k) (hf k)

/-- **Diagonal reduction of lower triangular matrices** whose corner lies in only countably
many maximal ideals. -/
theorem lower_hasSNF (A : Matrix (Fin 2) (Fin 2) R) (hA : A 0 1 = 0) (hu : Unimod A)
    (hcount : {M : Ideal R | M.IsMaximal ∧ A 0 0 ∈ M}.Countable) : HasSmithNormalForm A := by
  classical
  by_cases hne : {M : Ideal R | M.IsMaximal ∧ A 0 0 ∈ M}.Nonempty
  · obtain ⟨f, hf⟩ := hcount.exists_eq_range hne
    have hfmax : ∀ k, (f k).IsMaximal := fun k => by
      have : f k ∈ {M : Ideal R | M.IsMaximal ∧ A 0 0 ∈ M} := by rw [hf]; exact ⟨k, rfl⟩
      exact this.1
    set B₀ : LowerUni R := ⟨A, hA, hu⟩
    set S := seqLU B₀ f hfmax
    have hS0 : S 0 = B₀ := rfl
    have hSsucc : ∀ k, S (k + 1) = stepLU (S k) (f k) (hfmax k) := fun k => rfl
    have hmono : Monotone fun k => Ideal.span {(S k).1 0 0} := by
      refine monotone_nat_of_le_succ fun k => ?_
      rw [hSsucc]; exact (stepLU_spec _ _ _).2.2
    -- some corner is a unit
    have hunit : ∃ k, IsUnit ((S k).1 0 0) := by
      by_contra hcon
      push_neg at hcon
      set I := ⨆ k, Ideal.span {(S k).1 0 0}
      have hmem : ∀ z, z ∈ I ↔ ∃ k, z ∈ Ideal.span {(S k).1 0 0} := fun z =>
        Submodule.mem_iSup_of_directed _ hmono.directed_le
      have hI : I ≠ ⊤ := by
        intro h
        obtain ⟨k, hk⟩ := (hmem 1).1 (h ▸ Submodule.mem_top)
        exact hcon k (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 hk))
      obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I hI
      have hAJ : A 0 0 ∈ J := hIJ ((hmem _).2 ⟨0, Ideal.mem_span_singleton_self _⟩)
      have hJS : J ∈ {M : Ideal R | M.IsMaximal ∧ A 0 0 ∈ M} := ⟨hJ, hAJ⟩
      rw [hf] at hJS
      obtain ⟨k, rfl⟩ := hJS
      have h1 := (stepLU_spec (S k) (f k) (hfmax k)).2.1
      rw [← hSsucc] at h1
      exact h1 (hIJ ((hmem _).2 ⟨k + 1, Ideal.mem_span_singleton_self _⟩))
    obtain ⟨k, hk⟩ := hunit
    have hback : ∀ k, HasSmithNormalForm (S k).1 → HasSmithNormalForm A := by
      intro k
      induction k with
      | zero => exact id
      | succ k ih =>
        intro h
        rw [hSsucc] at h
        exact ih ((stepLU_spec _ _ _).1 h)
    exact hback k (hasSNF_of_unit_corner _ (S k).2.1 hk)
  · -- no maximal ideal contains the corner: it is a unit
    have hunit : IsUnit (A 0 0) := by
      by_contra hnu
      have hne' : Ideal.span {A 0 0} ≠ ⊤ := fun h => hnu (Ideal.span_singleton_eq_top.1 h)
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne'
      exact hne ⟨M, hM, hle (Ideal.mem_span_singleton_self _)⟩
    exact hasSNF_of_unit_corner A hA hunit

end Iter

end BezoutCounterexample

namespace BezoutCounterexample

open Matrix

section TwoByTwo

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]

variable (R) in
/-- The row swap. -/
def glSwap : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- Column Hermite reduction of the first row of a `2 × 2` matrix. -/
lemma exists_col_reduce (N : Matrix (Fin 2) (Fin 2) R) :
    ∃ (Q : GL (Fin 2) R) (h : R), (N * (Q : Matrix (Fin 2) (Fin 2) R)) 0 0 = h ∧
      (N * (Q : Matrix (Fin 2) (Fin 2) R)) 0 1 = 0 ∧
      (N 1 0 = 0 → N 1 1 = 0 → (N * (Q : Matrix (Fin 2) (Fin 2) R)) 1 0 = 0 ∧
        (N * (Q : Matrix (Fin 2) (Fin 2) R)) 1 1 = 0) := by
  obtain ⟨r, s, a', b', h, ha, hb, hrs⟩ := exists_bezout_data (N 0 0) (N 0 1)
  refine ⟨glTranspose (gl2 R r s a' b' hrs), h, ?_, ?_, fun h10 h11 => ⟨?_, ?_⟩⟩
  · simp [glTranspose, Matrix.mul_apply, Fin.sum_univ_two]
    rw [ha, hb]; linear_combination h * hrs
  · simp [glTranspose, Matrix.mul_apply, Fin.sum_univ_two]
    rw [ha, hb]; ring
  · simp [glTranspose, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
  · simp [glTranspose, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]

/-- Smith normal forms survive scaling by a common factor. -/
lemma HasSmithNormalForm.smul {m n : ℕ} {F : Matrix (Fin m) (Fin n) R}
    (h : HasSmithNormalForm F) (g : R) : HasSmithNormalForm (g • F) := by
  obtain ⟨G, ⟨P, Q, hPQ⟩, ⟨d, hd, hdiv⟩⟩ := h
  refine ⟨g • G, ⟨P, Q, ?_⟩, ⟨fun k => g * d k, fun i j => ?_, fun k hk =>
    mul_dvd_mul_left g (hdiv k hk)⟩⟩
  · rw [Matrix.mul_smul, Matrix.smul_mul, hPQ]
  · rw [Matrix.smul_apply, hd, smul_eq_mul]
    split_ifs <;> simp

/-- **Couchot's theorem for `2 × 2` matrices over domains**: over a Bézout domain of countable
character, every `2 × 2` matrix has a Smith normal form. -/
theorem hasSNF_two_of_countableCharacter (hcc : HasCountableCharacter R)
    (F : Matrix (Fin 2) (Fin 2) R) : HasSmithNormalForm F := by
  classical
  -- the content ideal is principal
  set c : Ideal R := Ideal.span (Set.range fun p : Fin 2 × Fin 2 => F p.1 p.2)
  obtain ⟨g, hg⟩ := (IsBezout.isPrincipal_of_FG c
    ⟨(Finset.univ.image fun p : Fin 2 × Fin 2 => F p.1 p.2), by simp [c]⟩).principal
  have hmemc : ∀ i j, F i j ∈ c := fun i j => Ideal.subset_span ⟨(i, j), rfl⟩
  by_cases hg0 : g = 0
  · -- `F = 0`
    have hF0 : F = 0 := by
      ext i j
      have := hmemc i j
      rw [hg, hg0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this
      exact this
    refine ⟨F, MatrixEquivalent.refl F, ⟨0, fun i j => ?_, fun k _ => dvd_refl _⟩⟩
    simp [hF0]
  -- divide out the content
  have hdiv : ∀ i j, ∃ x : R, F i j = g * x := fun i j => by
    have := hmemc i j
    rw [hg] at this
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨x, by rw [← hx, smul_eq_mul, mul_comm]⟩
  choose F' hF' using hdiv
  have hFg : F = g • Matrix.of F' := by ext i j; rw [hF']; rfl
  have hU : Unimod (Matrix.of F') := by
    intro I hI
    have hle : c ≤ I * Ideal.span {g} := by
      rw [Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      show F i j ∈ I * Ideal.span {g}
      rw [hF', mul_comm g]
      exact Ideal.mul_mem_mul (hI i j) (Ideal.mem_span_singleton_self g)
    have hgc : g ∈ c := by rw [hg]; exact Submodule.mem_span_singleton_self g
    obtain ⟨z, hz, hzg⟩ := Ideal.mem_mul_span_singleton.1 (hle hgc)
    have hz1 : z = 1 := mul_right_cancel₀ hg0 (by rw [hzg, one_mul])
    rw [hz1] at hz
    exact (Ideal.eq_top_iff_one I).2 hz
  rw [hFg]
  refine HasSmithNormalForm.smul ?_ g
  -- make the first row `(h, 0)`
  obtain ⟨Q, h, hL00, hL01, -⟩ := exists_col_reduce (Matrix.of F')
  set L := Matrix.of F' * (Q : Matrix (Fin 2) (Fin 2) R)
  have hLU : Unimod L := hU.equiv (MatrixEquivalent.mul_right Q)
  refine HasSmithNormalForm.of_equiv (MatrixEquivalent.mul_right Q) ?_
  by_cases hh : h = 0
  · -- the first row vanishes: swap the rows and reduce again
    set N := ((glSwap R : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * L
    have hN10 : N 1 0 = 0 := by
      simp [N, glSwap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hL00, hh]
    have hN11 : N 1 1 = 0 := by
      simp [N, glSwap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hL01]
    refine HasSmithNormalForm.of_equiv (MatrixEquivalent.mul_left (glSwap R)) ?_
    obtain ⟨Q', h', hD00, hD01, hD1⟩ := exists_col_reduce N
    obtain ⟨hD10, hD11⟩ := hD1 hN10 hN11
    refine ⟨N * (Q' : Matrix (Fin 2) (Fin 2) R), MatrixEquivalent.mul_right Q',
      ⟨fun k => if k = 0 then h' else 0, fun i j => ?_, fun k hk => ?_⟩⟩
    · fin_cases i <;> fin_cases j <;> simp [hD00, hD01, hD10, hD11]
    · have hk0 : k = 0 := by simp at hk; omega
      subst hk0
      simp
  · -- the corner lies in countably many maximal ideals
    have hcount : {M : Ideal R | M.IsMaximal ∧ L 0 0 ∈ M}.Countable := by
      rw [hL00]
      exact hcc h (mem_nonZeroDivisors_of_ne_zero hh)
    exact lower_hasSNF L hL01 hLU hcount

end TwoByTwo

end BezoutCounterexample

namespace BezoutCounterexample

/-- **Corollary 6.4** (`cor:not-countable-character`): the ring `R` of Construction 5.1 does not
have countable character; some nonzero element of the countable ring `R` belongs to uncountably
many maximal ideals.

The paper derives this from Couchot's theorem [Couchot, Thm. 12] and Theorem 1.1. Only the
`2 × 2` case of Couchot's theorem for domains is needed (`M` is a `2 × 2` matrix), and it is
proved above (`hasSNF_two_of_countableCharacter`). -/
theorem R.not_hasCountableCharacter (hPE : CoprimePairPE) :
    ¬ HasCountableCharacter (R hPE) ∧
      ∃ a : R hPE, a ≠ 0 ∧ ¬ {m : Ideal (R hPE) | m.IsMaximal ∧ a ∈ m}.Countable := by
  have h1 : ¬ HasCountableCharacter (R hPE) := fun h =>
    R.not_hasSmithNormalForm hPE (hasSNF_two_of_countableCharacter h _)
  refine ⟨h1, ?_⟩
  rw [hasCountableCharacter_iff] at h1
  push Not at h1
  exact h1

/-- **Corollary 6.4**, for the ring of Theorem 1.1 (Proposition 4.6 being proved). -/
theorem corollary_6_4 :
    ¬ HasCountableCharacter (R coprimePairPE_holds) ∧
      ∃ a : R coprimePairPE_holds, a ≠ 0 ∧
        ¬ {m : Ideal (R coprimePairPE_holds) | m.IsMaximal ∧ a ∈ m}.Countable :=
  R.not_hasCountableCharacter coprimePairPE_holds

end BezoutCounterexample

namespace BezoutCounterexample

open Matrix

section Explicit

variable {D : Type*} [CommRing D] [IsDomain D] [IsBezout D]

/-- If a unimodular `2 × 2` matrix over a Bézout domain has no Smith normal form, then
uncountably many maximal ideals contain its first row. -/
theorem not_countable_row_of_not_hasSNF (F : Matrix (Fin 2) (Fin 2) D) (hU : Unimod F)
    (hF : ¬ HasSmithNormalForm F) :
    ¬ {M : Ideal D | M.IsMaximal ∧ F 0 0 ∈ M ∧ F 0 1 ∈ M}.Countable := by
  intro hc
  obtain ⟨r, s, a', b', h, ha, hb, hrs⟩ := exists_bezout_data (F 0 0) (F 0 1)
  set Q := glTranspose (gl2 D r s a' b' hrs)
  set L := F * (Q : Matrix (Fin 2) (Fin 2) D)
  have hL00 : L 0 0 = h := by
    simp [L, Q, glTranspose, Matrix.mul_apply, Fin.sum_univ_two]
    rw [ha, hb]; linear_combination h * hrs
  have hL01 : L 0 1 = 0 := by
    simp [L, Q, glTranspose, Matrix.mul_apply, Fin.sum_univ_two]
    rw [ha, hb]; ring
  have hh : h = r * F 0 0 + s * F 0 1 := by rw [ha, hb]; linear_combination -h * hrs
  have hset : {M : Ideal D | M.IsMaximal ∧ L 0 0 ∈ M} =
      {M : Ideal D | M.IsMaximal ∧ F 0 0 ∈ M ∧ F 0 1 ∈ M} := by
    ext M
    simp only [Set.mem_setOf_eq, hL00]
    constructor
    · rintro ⟨hM, hhM⟩
      exact ⟨hM, by rw [ha]; exact M.mul_mem_left _ hhM, by rw [hb]; exact M.mul_mem_left _ hhM⟩
    · rintro ⟨hM, h0, h1⟩
      exact ⟨hM, by rw [hh]; exact M.add_mem (M.mul_mem_left _ h0) (M.mul_mem_left _ h1)⟩
  apply hF
  refine HasSmithNormalForm.of_equiv (MatrixEquivalent.mul_right Q) ?_
  exact lower_hasSNF L hL01 (hU.equiv (MatrixEquivalent.mul_right Q)) (hset ▸ hc)

end Explicit

/-- **Explicit form of Corollary 6.4**: uncountably many maximal ideals of `R` contain
`(1 + x, y)`, and uncountably many contain `(1 - x, y)`; in particular `1 + x`, `1 - x` and `y`
each lie in uncountably many maximal ideals. -/
theorem R.not_countable_maximal (hPE : CoprimePairPE) :
    ¬ {m : Ideal (R hPE) | m.IsMaximal ∧ R.ι hPE (1 + x) ∈ m ∧ R.ι hPE y ∈ m}.Countable ∧
      ¬ {m : Ideal (R hPE) | m.IsMaximal ∧ R.ι hPE (1 - x) ∈ m ∧ R.ι hPE y ∈ m}.Countable := by
  set F := M.map (R.ι hPE)
  have hF : ¬ HasSmithNormalForm F := R.not_hasSmithNormalForm hPE
  have hU : Unimod F := by
    intro I hI
    have h1 : R.ι hPE (1 + x) ∈ I := by simpa [F, M] using hI 0 0
    have h2 : R.ι hPE (1 - x) ∈ I := by simpa [F, M] using hI 1 1
    have h3 : R.ι hPE (1 + x) + R.ι hPE (1 - x) = algebraMap ℚ (R hPE) 2 := by
      rw [← map_add, show (1 + x) + (1 - x) = (2 : A₀) by ring, map_ofNat, map_ofNat]
    have hu : IsUnit (algebraMap ℚ (R hPE) 2) :=
      (isUnit_iff_ne_zero.2 (by norm_num : (2 : ℚ) ≠ 0)).map _
    exact Ideal.eq_top_of_isUnit_mem _ (h3 ▸ I.add_mem h1 h2) hu
  refine ⟨?_, ?_⟩
  · have := not_countable_row_of_not_hasSNF F hU hF
    simpa [F, M] using this
  · -- swap both rows and columns
    set S := ((glSwap (R hPE) : GL (Fin 2) (R hPE)) : Matrix (Fin 2) (Fin 2) (R hPE))
    have hEq : MatrixEquivalent F (S * F * S) := ⟨glSwap _, glSwap _, rfl⟩
    have hF' : ¬ HasSmithNormalForm (S * F * S) := fun h => hF (h.of_equiv hEq)
    have := not_countable_row_of_not_hasSNF _ (hU.equiv hEq) hF'
    simpa [S, F, M, glSwap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      using this

end BezoutCounterexample
