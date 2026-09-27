import BezoutCounterexample.Principalization.Vertex
import BezoutCounterexample.Principalization.DerivExt
import BezoutCounterexample.SplitConormal

/-!
# Smoothness of the local weighted Rees algebra

Over a local Noetherian `ℚ`-algebra `S` with a centred chart and a monomial weighting supported
on the first `k` coordinates, the extended Rees algebra is `S[s, u₀, …, u_{k-1}]/(xᵢ - s^{wᵢ} uᵢ)`
(`reesPsi_ker`), hence formally smooth over `ℚ` when `S` is (`rees_formallySmooth`). This is
Lemma 3.5 (4) (`lem:rees`) of the paper, which quotes the local structure from Quek–Rydh.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

section GradedCI

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}

/-- **Weighted `GradedCI`**: a weighted-homogeneous combination of monomials in the first `k`
coordinates of weight `j` lies in `𝓕_{(j+1)/d}` only if all its coefficients lie in
`(x₀, …, x_{k-1})`. -/
theorem gradedCI {c : Chart S n} (hc : c.IsCentred) {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {k : ℕ}
    (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) {d : ℕ} (hd : 0 < d) {w : Fin n → ℕ}
    (hw : ∀ i, (w i : ℚ) = d * e i) (j : ℕ) (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ α ∈ s, (∀ i : Fin n, k ≤ (i : ℕ) → α i = 0) ∧ Finsupp.weight w α = j)
    (q : (Fin n →₀ ℕ) → S)
    (hmem : ∑ α ∈ s, q α * ∏ i, c.x i ^ α i ∈ c.RF e (((j + 1 : ℕ) : ℚ) / d)) :
    ∀ α ∈ s, q α ∈ Ideal.span (c.x '' {i | (i : ℕ) < k}) := by
  classical
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hlamw : ∀ α : Fin n →₀ ℕ, lam e α = (Finsupp.weight w α : ℚ) / d := by
    intro α
    rw [lam, Finsupp.weight_eq_sum, eq_div_iff hdq.ne']
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Nat.cast_mul, hw i]; ring
  have hwpos : ∀ i : Fin n, (i : ℕ) < k → 0 < w i := by
    intro i hi
    have h1 := (hsupp i).2 hi
    have h2 := hw i
    have : (0 : ℚ) < w i := by rw [h2]; exact mul_pos hdq (lt_of_le_of_ne (he i) (Ne.symm h1))
    exact_mod_cast this
  intro α₀ hα₀
  rw [hc.mem_span_iff]
  intro β hβ
  -- the coefficient at `α₀ + β` of the combination vanishes
  have hlam : lam e (α₀ + β) < (((j + 1 : ℕ) : ℚ) / d) := by
    rw [lam_add, hlamw α₀, (hs α₀ hα₀).2]
    have hβ0 : lam e β = 0 := by
      rw [lam]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : (i : ℕ) < k
      · rw [hβ i hi, Nat.cast_zero, zero_mul]
      · rw [show e i = 0 by by_contra h; exact hi ((hsupp i).1 h), mul_zero]
    rw [hβ0, add_zero, div_lt_div_iff_of_pos_right hdq]
    exact_mod_cast Nat.lt_succ_self j
  have h0 := (hc.mem_RF_iff he _ _).1 hmem (α₀ + β) hlam
  rw [map_sum] at h0
  simp only [map_mul, hc.tau_monomial, map_sum] at h0
  rw [Finset.sum_eq_single α₀] at h0
  · rw [coeff_mul_monomial, ite_eq_left (le_add_right le_rfl), mul_one, add_tsub_cancel_left] at h0
    exact h0
  · intro α hα hne
    rw [coeff_mul_monomial]
    split_ifs with hle
    · exfalso
      apply hne
      -- `α ≤ α₀ + β` with equal weights forces `α = α₀`
      have hle' : α ≤ α₀ := by
        intro i
        by_cases hi : (i : ℕ) < k
        · have := hle i; simp only [Finsupp.add_apply, hβ i hi, add_zero] at this; exact this
        · rw [(hs α hα).1 i (by omega)]; exact Nat.zero_le _
      refine le_antisymm hle' ?_
      by_contra hlt
      have hlt' : α < α₀ := lt_of_le_of_ne hle' (fun h => hlt (h ▸ le_rfl))
      obtain ⟨i, hi⟩ : ∃ i, α i < α₀ i := by
        by_contra h; push Not at h; exact hlt (fun i => h i)
      have hik : (i : ℕ) < k := by
        by_contra h; push Not at h; rw [(hs α₀ hα₀).1 i h] at hi; omega
      have hwt : Finsupp.weight w α < Finsupp.weight w α₀ := by
        rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
        apply Finset.sum_lt_sum
        · intro l _; exact Nat.mul_le_mul_right _ (hle' l)
        · exact ⟨i, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_right hi (hwpos i hik)⟩
      rw [(hs α hα).2, (hs α₀ hα₀).2] at hwt
      exact lt_irrefl _ hwt
    · rfl
  · intro h; exact absurd hα₀ h

end GradedCI

end BezoutCounterexample.Principalization




namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesPres

variable {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}
variable (c : Chart S n) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil S} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n)

/-- The first `k` indices. -/
def ιk (hkn : k ≤ n) : Fin k → Fin n := fun i => ⟨i, lt_of_lt_of_le i.2 hkn⟩

lemma ιk_injective : Function.Injective (ιk hkn) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simpa [ιk] using this)

/-- The generators `s, u₀, …, u_{k-1}` of the Rees algebra. -/
def reesGen : Option (Fin k) → ReesAlg Φ := fun o =>
  o.elim (reesX c hF he hd hw (Fin.last n))
    (fun i => reesX c hF he hd hw (Fin.castSucc (ιk hkn i)))

/-- The presentation map `S[s, u] → ⊕ F_j T^j`. -/
def reesPsi : MvPolynomial (Option (Fin k)) S →ₐ[S] ReesAlg Φ :=
  MvPolynomial.aeval (reesGen c hF he hd hw hkn)

/-- The relations `xᵢ - s^{wᵢ} uᵢ`. -/
def reesRel (c : Chart S n) (w : Fin n → ℕ) (hkn : k ≤ n) :
    Fin k → MvPolynomial (Option (Fin k)) S := fun i =>
  MvPolynomial.C (c.x (ιk hkn i)) - X none ^ (w (ιk hkn i)) * X (some i)

lemma reesPsi_rel (i : Fin k) : reesPsi c hF he hd hw hkn (reesRel c w hkn i) = 0 := by
  rw [reesRel, map_sub, map_mul, map_pow, reesPsi, aeval_C, aeval_X, aeval_X]
  simp only [reesGen, Option.elim]
  rw [reesX_castSucc_mul_pow c hF he hd hw, mul_comm, sub_self]

include hw in
lemma w_eq_zero_of_ge (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) (j : Fin n) (hj : k ≤ (j : ℕ)) :
    w j = 0 := by
  have h := hw j
  have hej : e j = 0 := by by_contra h'; exact absurd ((hsupp j).1 h') (by omega)
  rw [hej, mul_zero] at h; exact_mod_cast h

lemma reesPsi_surjective (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) :
    Function.Surjective (reesPsi c hF he hd hw hkn) := by
  have hle : Algebra.adjoin S (Set.range (reesX c hF he hd hw)) ≤
      (reesPsi c hF he hd hw hkn).range := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last =>
      refine ⟨X none, ?_⟩
      show reesPsi c hF he hd hw hkn (X none) = _
      rw [reesPsi, aeval_X]; rfl
    | cast j =>
      by_cases hj : (j : ℕ) < k
      · refine ⟨X (some ⟨j, hj⟩), ?_⟩
        show reesPsi c hF he hd hw hkn (X (some ⟨j, hj⟩)) = _
        rw [reesPsi, aeval_X]; rfl
      · have hw0 := w_eq_zero_of_ge hw hsupp j (by omega)
        refine ⟨MvPolynomial.C (c.x j), ?_⟩
        show reesPsi c hF he hd hw hkn (MvPolynomial.C (c.x j)) = _
        rw [reesPsi, aeval_C]
        have := reesX_castSucc_mul_pow c hF he hd hw j
        rw [hw0, pow_zero, mul_one] at this
        exact this
  rw [rees_adjoin] at hle
  intro y; exact hle Algebra.mem_top

end ReesPres

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesTorsion

variable {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}
variable (c : Chart S n) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil S} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n)

/-- Every polynomial is, after multiplication by a power of `s`, congruent modulo the relations to
a polynomial in `s` alone. -/
lemma rees_reduce (p : MvPolynomial (Option (Fin k)) S) :
    ∃ (N : ℕ) (f : Polynomial S), X none ^ N * p - Polynomial.aeval (X none) f ∈
      Ideal.span (Set.range (reesRel c w hkn)) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, Polynomial.C a, by simp⟩
  | add p q hp hq =>
    obtain ⟨Np, fp, hfp⟩ := hp
    obtain ⟨Nq, fq, hfq⟩ := hq
    refine ⟨Np + Nq, Polynomial.X ^ Nq * fp + Polynomial.X ^ Np * fq, ?_⟩
    have : X none ^ (Np + Nq) * (p + q) - Polynomial.aeval (X none)
        (Polynomial.X ^ Nq * fp + Polynomial.X ^ Np * fq) =
        X none ^ Nq * (X none ^ Np * p - Polynomial.aeval (X none) fp) +
          X none ^ Np * (X none ^ Nq * q - Polynomial.aeval (X none) fq) := by
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_X]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hfp) (Ideal.mul_mem_left _ _ hfq)
  | mul_X p o hp =>
    obtain ⟨N, f, hf⟩ := hp
    cases o with
    | none =>
      refine ⟨N, f * Polynomial.X, ?_⟩
      have : X none ^ N * (p * X none) - Polynomial.aeval (X none) (f * Polynomial.X) =
          (X none ^ N * p - Polynomial.aeval (X none) f) * X none := by
        simp only [map_mul, Polynomial.aeval_X]; ring
      rw [this]; exact Ideal.mul_mem_right _ _ hf
    | some i =>
      refine ⟨N + w (ιk hkn i), f * Polynomial.C (c.x (ιk hkn i)), ?_⟩
      have hr : reesRel c w hkn i ∈ Ideal.span (Set.range (reesRel c w hkn)) :=
        Ideal.subset_span ⟨i, rfl⟩
      have : X none ^ (N + w (ιk hkn i)) * (p * X (some i)) -
          Polynomial.aeval (X none) (f * Polynomial.C (c.x (ιk hkn i))) =
          (X none ^ N * p - Polynomial.aeval (X none) f) *
            (X none ^ w (ιk hkn i) * X (some i)) -
          Polynomial.aeval (X none) f * reesRel c w hkn i := by
        simp only [reesRel, map_mul, Polynomial.aeval_C, MvPolynomial.algebraMap_eq]; ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ hr)

lemma reesPsi_rel_le : Ideal.span (Set.range (reesRel c w hkn)) ≤
    RingHom.ker (reesPsi c hF he hd hw hkn) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact reesPsi_rel c hF he hd hw hkn i

omit [Algebra ℚ S] in
lemma aeval_Tinv_coeff (f : Polynomial S) (i : ℕ) :
    (Polynomial.aeval (T (-1) : S[T;T⁻¹]) f).coeff (-(i : ℤ)) = f.coeff i := by
  classical
  rw [Polynomial.aeval_eq_sum_range, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  have hterm : ∀ j, (f.coeff j • (T (-1) : S[T;T⁻¹]) ^ j).coeff (-(i : ℤ)) =
      if j = i then f.coeff j else 0 := by
    intro j
    rw [T_pow, AddMonoidAlgebra.coeff_smul_apply, T_apply]
    by_cases h : j = i
    · subst h; simp
    · rw [ite_eq_right (by omega), ite_eq_right h, smul_zero]
  simp only [hterm]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    simp only [Finset.mem_range, not_lt] at h; omega

omit [Algebra ℚ S] in
lemma aeval_Tinv_injective (f : Polynomial S) (hf : Polynomial.aeval (T (-1) : S[T;T⁻¹]) f = 0) :
    f = 0 := by
  ext i
  rw [← aeval_Tinv_coeff, hf]; rfl

/-- **Torsion**: elements of the kernel are killed by a power of `s` modulo the relations. -/
theorem rees_torsion (p : MvPolynomial (Option (Fin k)) S)
    (hp : reesPsi c hF he hd hw hkn p = 0) :
    ∃ N : ℕ, X none ^ N * p ∈ Ideal.span (Set.range (reesRel c w hkn)) := by
  obtain ⟨N, f, hf⟩ := rees_reduce c hkn p
  refine ⟨N, ?_⟩
  have h1 := reesPsi_rel_le c hF he hd hw hkn hf
  rw [RingHom.mem_ker, map_sub, map_mul, hp, mul_zero, zero_sub, neg_eq_zero] at h1
  have h2 : (reesPsi c hF he hd hw hkn (Polynomial.aeval (X none) f) : S[T;T⁻¹]) =
      Polynomial.aeval (T (-1) : S[T;T⁻¹]) f := by
    rw [← Polynomial.aeval_algHom_apply]
    have : (reesPsi c hF he hd hw hkn) (X none) = reesX c hF he hd hw (Fin.last n) := by
      rw [reesPsi, aeval_X]; rfl
    rw [this]
    change (ReesAlg Φ).val (Polynomial.aeval (reesX c hF he hd hw (Fin.last n)) f) = _
    rw [← Polynomial.aeval_algHom_apply]
    congr 2
    exact reesX_last c hF he hd hw
  have hf0 : f = 0 := by
    apply aeval_Tinv_injective
    rw [← h2, h1]; rfl
  have : X none ^ N * p = X none ^ N * p - Polynomial.aeval (X none) f := by
    rw [hf0, map_zero, sub_zero]
  rw [this]; exact hf

end ReesTorsion

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesStepA

variable {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}
variable (c : Chart S n) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil S} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n)

/-- Setting `s = 0`. -/
def evS0 : MvPolynomial (Option (Fin k)) S →ₐ[S] MvPolynomial (Fin k) S :=
  MvPolynomial.aeval (fun o => o.elim 0 X)

omit [Algebra ℚ S] in
lemma sub_rename_evS0_mem (p : MvPolynomial (Option (Fin k)) S) :
    p - rename some (evS0 p) ∈ Ideal.span {(X none : MvPolynomial (Option (Fin k)) S)} := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evS0]
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]; exact Ideal.add_mem _ hp hq
  | mul_X p o hp =>
    rw [map_mul, map_mul]
    have : p * X o - rename some (evS0 p) * rename some (evS0 (X o)) =
        (p - rename some (evS0 p)) * X o +
          rename some (evS0 p) * (X o - rename some (evS0 (X o))) := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    cases o with
    | none => simp [evS0]
    | some i => simp [evS0]

/-- The weight of a multi-index in the first `k` variables. -/
def wk (hkn : k ≤ n) (w : Fin n → ℕ) (α : Fin k →₀ ℕ) : ℕ := ∑ i, α i * w (ιk hkn i)

lemma prod_reesU (α : Fin k →₀ ℕ) :
    ∏ i, ((reesX c hF he hd hw (Fin.castSucc (ιk hkn i)) : ReesAlg Φ) : S[T;T⁻¹]) ^ α i =
      LaurentPolynomial.C (∏ i, c.x (ιk hkn i) ^ α i) * T (wk hkn w α) := by
  simp only [reesX_castSucc, mul_pow, T_pow, ← map_pow]
  rw [Finset.prod_mul_distrib, ← map_prod, prod_T_eq, wk]
  push_cast; rfl

/-- The coefficients of the image of an `s`-free polynomial. -/
lemma coeff_reesPsi_rename (q : MvPolynomial (Fin k) S) (j : ℤ) :
    ((reesPsi c hF he hd hw hkn (rename some q) : ReesAlg Φ) : S[T;T⁻¹]).coeff j =
      ∑ α ∈ q.support, if (wk hkn w α : ℤ) = j then
        q.coeff α * ∏ i, c.x (ιk hkn i) ^ α i else 0 := by
  have h1 : reesPsi c hF he hd hw hkn (rename some q) =
      MvPolynomial.aeval (fun i => reesX c hF he hd hw (Fin.castSucc (ιk hkn i))) q := by
    rw [reesPsi, aeval_rename]; rfl
  rw [h1]
  change ((ReesAlg Φ).val (MvPolynomial.aeval _ q)).coeff j = _
  rw [MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun α _ => ?_
  have h2 := prod_reesU c hF he hd hw hkn α
  simp only [Subalgebra.coe_val] at h2 ⊢
  rw [h2, ← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul, coeff_C_mul_T]
  by_cases h : j = (wk hkn w α : ℤ)
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

end ReesStepA

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesStepA2

variable {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ} {k : ℕ} (hkn : k ≤ n)

lemma mapDomain_ιk_apply_ge (α : Fin k →₀ ℕ) (j : Fin n) (hj : k ≤ (j : ℕ)) :
    Finsupp.mapDomain (ιk hkn) α j = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, rfl⟩
  simp [ιk] at hj; omega

lemma weight_mapDomain_ιk (w : Fin n → ℕ) (α : Fin k →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain (ιk hkn) α) = wk hkn w α := by
  induction α using Finsupp.induction_linear with
  | zero => simp [wk]
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add, map_add, ha, hb, wk, wk, wk, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.add_apply, add_mul]
  | single i m =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, wk, Finset.sum_eq_single i]
    · simp [smul_eq_mul]
    · intro b _ hb; rw [Finsupp.single_apply, ite_eq_right (Ne.symm hb), zero_mul]
    · simp

lemma prod_mapDomain_ιk {R : Type*} [CommMonoid R] (x : Fin n → R) (α : Fin k →₀ ℕ) :
    ∏ j, x j ^ (Finsupp.mapDomain (ιk hkn) α) j = ∏ i, x (ιk hkn i) ^ α i := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, ha, hb]
  | single i m =>
    rw [Finsupp.mapDomain_single, Finset.prod_eq_single (ιk hkn i), Finset.prod_eq_single i]
    · simp
    · intro b _ hb; rw [Finsupp.single_apply, ite_eq_right (Ne.symm hb), pow_zero]
    · simp
    · intro b _ hb; rw [Finsupp.single_apply, ite_eq_right (Ne.symm hb), pow_zero]
    · simp

end ReesStepA2

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesStepA3

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}
variable {c : Chart S n} (hc : c.IsCentred) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  (he : ∀ i, 0 ≤ e i) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n)
  (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)

include hc he hd hw hsupp in
theorem gradedCI_k (j : ℕ) (q : MvPolynomial (Fin k) S)
    (hmem : ∑ α ∈ q.support, (if wk hkn w α = j then
      q.coeff α * ∏ i, c.x (ιk hkn i) ^ α i else 0) ∈ c.RF e (((j + 1 : ℕ) : ℚ) / d)) :
    ∀ α ∈ q.support, wk hkn w α = j → q.coeff α ∈ Ideal.span (c.x '' {i | (i : ℕ) < k}) := by
  classical
  set emb : (Fin k →₀ ℕ) ↪ (Fin n →₀ ℕ) :=
    ⟨Finsupp.mapDomain (ιk hkn), Finsupp.mapDomain_injective (ιk_injective hkn)⟩ with hemb
  set s := (q.support.filter (fun α => wk hkn w α = j)).map emb with hsdef
  set Q' : (Fin n →₀ ℕ) → S := fun α' =>
    q.coeff (Finsupp.comapDomain (ιk hkn) α' (ιk_injective hkn).injOn) with hQ'
  have hQ'emb : ∀ α, Q' (emb α) = q.coeff α := fun α => by
    simp only [hQ', hemb, Function.Embedding.coeFn_mk, Finsupp.comapDomain_mapDomain _
      (ιk_injective hkn)]
  have hs : ∀ α' ∈ s, (∀ i : Fin n, k ≤ (i : ℕ) → α' i = 0) ∧ Finsupp.weight w α' = j := by
    intro α' hα'
    rw [hsdef, Finset.mem_map] at hα'
    obtain ⟨α, hα, rfl⟩ := hα'
    rw [Finset.mem_filter] at hα
    exact ⟨fun i hi => mapDomain_ιk_apply_ge hkn α i hi, by
      show Finsupp.weight w (Finsupp.mapDomain (ιk hkn) α) = j
      rw [weight_mapDomain_ιk]; exact hα.2⟩
  have hmem' : ∑ α' ∈ s, Q' α' * ∏ i, c.x i ^ α' i ∈ c.RF e (((j + 1 : ℕ) : ℚ) / d) := by
    have hQ'md : ∀ α, Q' (Finsupp.mapDomain (ιk hkn) α) = q.coeff α := hQ'emb
    rw [hsdef, Finset.sum_map]
    simp only [hemb, Function.Embedding.coeFn_mk, prod_mapDomain_ιk, hQ'md]
    rw [Finset.sum_filter]
    exact hmem
  have key := gradedCI hc he hsupp hd hw j s hs Q' hmem'
  intro α hα hwα
  have := key (emb α) (by
    rw [hsdef, Finset.mem_map]; exact ⟨α, Finset.mem_filter.2 ⟨hα, hwα⟩, rfl⟩)
  rwa [hQ'emb] at this

end ReesStepA3

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesStepA4

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}
variable (c : Chart S n) (hc : c.IsCentred) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil S} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n)
  (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)

include hd hw hsupp in
omit [IsLocalRing S] [IsNoetherianRing S] in
lemma C_mem_rel_sup (a : S) (ha : a ∈ Ideal.span (c.x '' {i | (i : ℕ) < k})) :
    (MvPolynomial.C a : MvPolynomial (Option (Fin k)) S) ∈
      Ideal.span (Set.range (reesRel c w hkn)) ⊔ Ideal.span {X none} := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    set i : Fin k := ⟨j, hj⟩
    have hij : ιk hkn i = j := Fin.ext rfl
    have hwj : 1 ≤ w j := by
      have h1 := (hsupp j).2 hj
      have h2 := hw j
      by_contra h; push Not at h
      have : w j = 0 := by omega
      rw [this, Nat.cast_zero, eq_comm, mul_eq_zero] at h2
      rcases h2 with h2 | h2
      · exact absurd h2 (by exact_mod_cast hd.ne')
      · exact h1 h2
    have : (MvPolynomial.C (c.x j) : MvPolynomial (Option (Fin k)) S) =
        reesRel c w hkn i + X none ^ w (ιk hkn i) * X (some i) := by
      rw [reesRel, hij]; ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mem_sup_right ?_)
    rw [hij, show w j = (w j - 1) + 1 by omega, pow_succ, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul b x _ hx => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx

include hc hsupp in
/-- **Step A**: modulo the relations, elements of the kernel are divisible by `s` with quotient in the
kernel. -/
theorem rees_stepA (p : MvPolynomial (Option (Fin k)) S) (hp : reesPsi c hF he hd hw hkn p = 0) :
    ∃ p', reesPsi c hF he hd hw hkn p' = 0 ∧
      p - X none * p' ∈ Ideal.span (Set.range (reesRel c w hkn)) := by
  classical
  set q := evS0 p with hq
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (sub_rename_evS0_mem p)
  -- `Ψ(q) ∈ s · R`
  have hΨ : reesPsi c hF he hd hw hkn (rename some q) =
      -(reesX c hF he hd hw (Fin.last n) * reesPsi c hF he hd hw hkn t) := by
    have h1 : rename some q = p - t * X none := by rw [ht]; ring
    rw [h1, map_sub, hp, zero_sub, map_mul]
    have : reesPsi c hF he hd hw hkn (X none) = reesX c hF he hd hw (Fin.last n) := by
      rw [reesPsi, aeval_X]; rfl
    rw [this, mul_comm]
  have hmem : ∀ j : ℕ, ∑ α ∈ q.support, (if wk hkn w α = j then
      q.coeff α * ∏ i, c.x (ιk hkn i) ^ α i else 0) ∈ c.RF e (((j + 1 : ℕ) : ℚ) / d) := by
    intro j
    have h1 := coeff_reesPsi_rename c hF he hd hw hkn q j
    rw [hΨ] at h1
    have h2 : ((-(reesX c hF he hd hw (Fin.last n) * reesPsi c hF he hd hw hkn t) :
        ReesAlg Φ) : S[T;T⁻¹]).coeff j =
        -((reesPsi c hF he hd hw hkn t : ReesAlg Φ) : S[T;T⁻¹]).coeff (j + 1) := by
      rw [NegMemClass.coe_neg, Subalgebra.coe_mul, reesX_last, AddMonoidAlgebra.coeff_neg,
        Finsupp.neg_apply, coeff_T_mul]
      ring_nf
    rw [h2] at h1
    have h3 := (reesPsi c hF he hd hw hkn t).2 ((j : ℤ) + 1)
    rw [hF] at h3
    simp only [Nat.cast_add, Nat.cast_one]
    have : (∑ α ∈ q.support, if (wk hkn w α : ℤ) = (j : ℤ) then
        q.coeff α * ∏ i, c.x (ιk hkn i) ^ α i else 0) =
        ∑ α ∈ q.support, if wk hkn w α = j then
        q.coeff α * ∏ i, c.x (ιk hkn i) ^ α i else 0 :=
      Finset.sum_congr rfl fun α _ => by simp only [Nat.cast_inj]
    rw [← this, ← h1]
    exact neg_mem (by simpa [chartFil] using h3)
  have hcoef : ∀ α ∈ q.support, q.coeff α ∈ Ideal.span (c.x '' {i | (i : ℕ) < k}) :=
    fun α hα => gradedCI_k hc he hd hw hkn hsupp (wk hkn w α) q (hmem _) α hα rfl
  -- `rename some q` lies in `(relations) + (s)`
  have hrq : rename some q ∈ Ideal.span (Set.range (reesRel c w hkn)) ⊔ Ideal.span {X none} := by
    have hq_sum : rename some q = ∑ α ∈ q.support, rename some (monomial α (q.coeff α)) := by
      conv_lhs => rw [q.as_sum]
      rw [map_sum]
    rw [hq_sum]
    refine Ideal.sum_mem _ fun α hα => ?_
    rw [rename_monomial, show monomial (Finsupp.mapDomain some α) (q.coeff α) =
      MvPolynomial.C (q.coeff α) * monomial (Finsupp.mapDomain some α) 1 by
        rw [C_mul_monomial, mul_one]]
    exact Ideal.mul_mem_right _ _ (C_mem_rel_sup c hd hw hkn hsupp _ (hcoef α hα))
  have hpmem : p ∈ Ideal.span (Set.range (reesRel c w hkn)) ⊔ Ideal.span {X none} := by
    have : p = rename some q + X none * t := by linear_combination -ht
    rw [this]
    exact Ideal.add_mem _ hrq (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  obtain ⟨k₀, hk₀, z, hz, hkz⟩ := Submodule.mem_sup.1 hpmem
  obtain ⟨p', rfl⟩ := Ideal.mem_span_singleton'.1 hz
  refine ⟨p', ?_, ?_⟩
  · have h1 := congrArg (reesPsi c hF he hd hw hkn) hkz
    rw [hp, map_add, reesPsi_rel_le c hF he hd hw hkn hk₀, zero_add, map_mul] at h1
    have hX : reesPsi c hF he hd hw hkn (X none) = reesX c hF he hd hw (Fin.last n) := by
      rw [reesPsi, aeval_X]; rfl
    rw [hX] at h1
    apply Subtype.ext
    have h2 : (T (-1) : S[T;T⁻¹]) * ((reesPsi c hF he hd hw hkn p' : ReesAlg Φ) : S[T;T⁻¹]) = 0 := by
      have := congrArg (fun y : ReesAlg Φ => (y : S[T;T⁻¹])) h1
      simp only [Subalgebra.coe_mul, reesX_last, ZeroMemClass.coe_zero] at this
      rw [mul_comm]; exact this
    exact (isUnit_T (-1)).mul_right_eq_zero.1 h2
  · have : p - p' * X none = k₀ := by rw [← hkz]; ring
    rw [mul_comm, this]; exact hk₀

end ReesStepA4

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesKer

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}
variable (c : Chart S n) (hc : c.IsCentred) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil S} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n)
  (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)

include hc hsupp in
/-- **The Rees algebra of a centre is presented by the relations `xᵢ = s^{wᵢ} uᵢ`.** -/
theorem reesPsi_ker :
    RingHom.ker (reesPsi c hF he hd hw hkn) = Ideal.span (Set.range (reesRel c w hkn)) := by
  classical
  refine le_antisymm ?_ (reesPsi_rel_le c hF he hd hw hkn)
  set K₀ := Ideal.span (Set.range (reesRel c w hkn))
  set π := Ideal.Quotient.mk K₀
  set Kb : Ideal (MvPolynomial (Option (Fin k)) S ⧸ K₀) :=
    (RingHom.ker (reesPsi c hF he hd hw hkn)).map π with hKb
  set sb := π (X none) with hsb
  -- `K̄ ⊆ s̄ K̄`
  have hle : Kb ≤ Ideal.span {sb} • Kb := by
    intro y hy
    rw [hKb, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    obtain ⟨p', hp', hk⟩ := rees_stepA c hc hF he hd hw hkn hsupp p hp
    have : π p = sb * π p' := by
      rw [hsb, ← map_mul, Ideal.Quotient.eq]; exact hk
    rw [this, smul_eq_mul]
    exact Ideal.mul_mem_mul (Ideal.subset_span rfl) (Ideal.mem_map_of_mem _ hp')
  -- torsion
  have htor : ∀ y ∈ Kb, ∃ N : ℕ, sb ^ N * y = 0 := by
    intro y hy
    rw [hKb, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    obtain ⟨N, hN⟩ := rees_torsion c hF he hd hw hkn p hp
    exact ⟨N, by rw [hsb, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hN⟩
  -- Nakayama
  have hfg : (Kb : Submodule _ _).FG := IsNoetherian.noetherian _
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {sb}) (Kb : Submodule _ _) hfg hle
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hr1
  have hK0 : Kb = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨N, hN⟩ := htor y hy
    have hy1 : y = (-(b * sb)) * y := by
      have := hr y hy
      rw [smul_eq_mul] at this
      have hr' : r = 1 + b * sb := by rw [hb]; ring
      rw [hr'] at this
      linear_combination this
    have hyN : ∀ m : ℕ, y = (-(b * sb)) ^ m * y := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, mul_assoc, ← hy1, ← ih]
    rw [Ideal.mem_bot]
    calc y = (-(b * sb)) ^ N * y := hyN N
      _ = (-b) ^ N * (sb ^ N * y) := by ring
      _ = 0 := by rw [hN, mul_zero]
  intro p hp
  have : π p ∈ Kb := Ideal.mem_map_of_mem _ hp
  rw [hK0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end ReesKer

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial MvPolynomial IsLocalRing

section ReesSmooth

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}
variable (c : Chart S n) (hc : c.IsCentred) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil S} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n)
  (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)

omit [IsLocalRing S] [IsNoetherianRing S] in
lemma mapCoeffs_X_mul (δ : Derivation ℚ S S) (a : ℕ) (o : Option (Fin k)) :
    BezoutCounterexample.mapCoeffs δ (X none ^ a * X o : MvPolynomial (Option (Fin k)) S) = 0 := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, BezoutCounterexample.mapCoeffs_X,
    BezoutCounterexample.mapCoeffs_X]
  simp

include hc hF he hd hw hkn hsupp in
/-- **The local Rees algebra is formally smooth.** -/
theorem rees_formallySmooth [Algebra.FormallySmooth ℚ S] :
    Algebra.FormallySmooth ℚ (ReesAlg Φ) := by
  classical
  set K₀ := Ideal.span (Set.range (reesRel c w hkn))
  have : Algebra.FormallySmooth S (MvPolynomial (Option (Fin k)) S) := inferInstance
  have : Algebra.FormallySmooth ℚ (MvPolynomial (Option (Fin k)) S) :=
    Algebra.FormallySmooth.comp ℚ S _
  let D : Fin k → Derivation ℚ (MvPolynomial (Option (Fin k)) S)
      (MvPolynomial (Option (Fin k)) S ⧸ K₀) := fun i =>
    ((Ideal.Quotient.mkₐ (MvPolynomial (Option (Fin k)) S) K₀).toLinearMap).compDer
      (BezoutCounterexample.mapCoeffs (c.d (ιk hkn i)))
  have hD : ∀ i j, D i (reesRel c w hkn j) = if i = j then 1 else 0 := by
    intro i j
    have hDv : ∀ p, D i p = Ideal.Quotient.mk K₀
        (BezoutCounterexample.mapCoeffs (c.d (ιk hkn i)) p) := fun p => rfl
    rw [hDv]
    simp only [reesRel, map_sub, BezoutCounterexample.mapCoeffs_C, mapCoeffs_X_mul, sub_zero]
    rw [c.d_x]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right (fun h => hij (ιk_injective hkn h)), ite_eq_right hij]; simp
  have := formallySmooth_quotient_of_dual (R := ℚ) (reesRel c w hkn) D hD
  have hker := reesPsi_ker c hc hF he hd hw hkn hsupp
  let e₁ : (MvPolynomial (Option (Fin k)) S ⧸ K₀) ≃ₐ[S] ReesAlg Φ :=
    (Ideal.quotientEquivAlgOfEq S hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (reesPsi_surjective c hF he hd hw hkn hsupp))
  exact Algebra.FormallySmooth.of_equiv (e₁.restrictScalars ℚ)

end ReesSmooth

end BezoutCounterexample.Principalization

