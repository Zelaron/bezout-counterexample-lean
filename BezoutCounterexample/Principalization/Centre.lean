import BezoutCounterexample.Principalization.Duality

/-!
# Marked centres and the uniqueness of the maximal admissible centre

For a Noetherian local `ℚ`-algebra with a centred chart we consider *marked centres*
`(x₀^{1/e₀}, x₁^{1/e₁}, …)`, given by a centred chart and antitone nonnegative weights `e`, with
weighted ideals `RF e t = (x^α : ∑ αᵢ eᵢ ≥ t)`.  We prove:

* rational weighted duality (`Chart.IsCentred.mem_RF_iff`);
* the monomial and derivation criteria comparing weighted ideals of two charts, the replacement
  lemma `Chart.IsCentred.RF_replace` and the fundamental chain rule lemmas;
* **Method 1** of Brais (inductive construction of semi-associated centres, `MC.SA.step`);
* **uniqueness of the maximal admissible marked centre** (`MC.exists_max`), the key canonicity
  statement of Abramovich–Temkin–Włodarczyk (Thm. 5.3.1).

This is Theorem 3.3 (1) (`thm:invariant`) of the paper, which quotes it from ATW and Brais.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

/-- `λ_e(α) = ∑ αᵢ eᵢ`. -/
def lam (e : Fin n → ℚ) (α : Fin n →₀ ℕ) : ℚ := ∑ i, (α i : ℚ) * e i

lemma lam_add (e : Fin n → ℚ) (α β : Fin n →₀ ℕ) : lam e (α + β) = lam e α + lam e β := by
  simp only [lam, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

lemma lam_single (e : Fin n → ℚ) (i : Fin n) (k : ℕ) : lam e (Finsupp.single i k) = k * e i := by
  rw [lam, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

lemma lam_zero (e : Fin n → ℚ) : lam e 0 = 0 := by simp [lam]

lemma lam_nonneg {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (α : Fin n →₀ ℕ) : 0 ≤ lam e α :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (he i)

namespace Chart

variable (c : Chart R n)

/-- Rational weighted monomial ideal `𝓕_t(c, e) = (x^α : α supported on {eᵢ ≠ 0}, λ_e(α) ≥ t)`. -/
def RF (e : Fin n → ℚ) (t : ℚ) : Ideal R :=
  Ideal.span {f | ∃ α : Fin n →₀ ℕ, (∀ i, e i = 0 → α i = 0) ∧ t ≤ lam e α ∧
    f = ∏ i, c.x i ^ α i}

lemma RF_antitone (e : Fin n → ℚ) {s t : ℚ} (h : s ≤ t) : c.RF e t ≤ c.RF e s :=
  Ideal.span_mono fun _ ⟨α, h0, ht, hf⟩ => ⟨α, h0, h.trans ht, hf⟩

lemma RF_of_nonpos {e : Fin n → ℚ} (_he : ∀ i, 0 ≤ e i) {t : ℚ} (ht : t ≤ 0) : c.RF e t = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, fun _ _ => rfl, by rw [lam_zero]; exact ht, by simp⟩

lemma RF_mul_le (e : Fin n → ℚ) (s t : ℚ) : c.RF e s * c.RF e t ≤ c.RF e (s + t) := by
  rw [RF, RF, Ideal.span_mul_span, RF]
  refine Ideal.span_mono ?_
  rintro _ ⟨a, ⟨α, h0, hs, rfl⟩, b, ⟨α', h0', ht, rfl⟩, rfl⟩
  refine ⟨α + α', fun i hi => by rw [Finsupp.add_apply, h0 i hi, h0' i hi], by
    rw [lam_add]; linarith, ?_⟩
  simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

lemma x_mem_RF (e : Fin n → ℚ) (i : Fin n) (hi : e i ≠ 0) : c.x i ∈ c.RF e (e i) := by
  refine Ideal.subset_span ⟨Finsupp.single i 1, fun l hl => ?_, by rw [lam_single]; simp, ?_⟩
  · rw [Finsupp.single_apply, ite_eq_right]; rintro rfl; exact hi hl
  · rw [Finset.prod_eq_single i]
    · simp
    · intro l _ hl; rw [Finsupp.single_apply, ite_eq_right (Ne.symm hl), pow_zero]
    · simp

/-- Scaling rational weights to integer weights. -/
lemma exists_scale {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) :
    ∃ (d : ℕ) (w : Fin n → ℕ), 0 < d ∧ ∀ i, (w i : ℚ) = d * e i := by
  set D := ∏ j, (e j).den with hD
  have hdvd : ∀ i, (e i).den ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨D, fun i => (e i).num.toNat * (D / (e i).den),
    Finset.prod_pos fun i _ => (e i).den_pos, fun i => ?_⟩
  have hnn : 0 ≤ (e i).num := Rat.num_nonneg.2 (he i)
  have hden : ((e i).den : ℚ) ≠ 0 := by exact_mod_cast (e i).den_pos.ne'
  rw [Nat.cast_mul, Nat.cast_div (hdvd i) hden]
  have h1 : (((e i).num.toNat : ℕ) : ℚ) = (e i).num := by exact_mod_cast Int.toNat_of_nonneg hnn
  rw [h1]
  conv_rhs => rw [← Rat.num_div_den (e i)]
  field_simp

lemma RF_eq_F {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} (hd : 0 < d)
    (hw : ∀ i, (w i : ℚ) = d * e i) (t : ℚ) : c.RF e t = c.F w ⌈(d : ℚ) * t⌉₊ := by
  have hlam : ∀ α : Fin n →₀ ℕ, (Finsupp.weight w α : ℚ) = d * lam e α := by
    intro α
    rw [Finsupp.weight_eq_sum, lam, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Nat.cast_mul, hw i]; ring
  have hzero : ∀ i, w i = 0 ↔ e i = 0 := by
    intro i
    have h := hw i
    constructor
    · intro h0; rw [h0, Nat.cast_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left (by positivity)
    · intro h0; rw [h0, mul_zero] at h; exact_mod_cast h
  rw [RF, F]
  congr 1
  ext f
  simp only [wmonos, Set.mem_ofPred_eq]
  refine exists_congr fun α => and_congr (forall_congr' fun i => by rw [hzero i]) ?_
  refine and_congr ?_ Iff.rfl
  rw [Nat.ceil_le, hlam]
  constructor
  · intro h; exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  · intro h; exact le_of_mul_le_mul_left h (by exact_mod_cast hd)

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

/-- Induction on multi-indices by adding unit vectors. -/
lemma Finsupp.induction_single {P : (Fin n →₀ ℕ) → Prop} (h0 : P 0)
    (hs : ∀ β i, P β → P (β + Finsupp.single i 1)) : ∀ β, P β := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β ih =>
    by_cases hβ : β = 0
    · subst hβ; exact h0
    · obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by
        by_contra h; push Not at h; exact hβ (Finsupp.ext h)
      set β' := β - Finsupp.single i 1 with hβ'
      have hsum : β' + Finsupp.single i 1 = β := by
        ext l
        simp only [hβ', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
      have hlt : β' < β := by
        rw [← hsum]
        exact lt_add_of_pos_right _ (lt_of_le_of_ne zero_le
          (Ne.symm (Finsupp.single_ne_zero.2 one_ne_zero)))
      rw [← hsum]; exact hs β' i (ih β' hlt)

namespace Chart

variable (c : Chart R n)

lemma D_d (β : Fin n →₀ ℕ) (i : Fin n) (f : R) : c.D β (c.d i f) = c.d i (c.D β f) := by
  rw [← D_add_single]
  simp only [D, dpow_add, dpow_single, pow_one]
  rfl

lemma Dv_d (β : Fin n →₀ ℕ) (i : Fin n) (f : R) : c.Dv β (c.d i f) = c.d i (c.Dv β f) := by
  simp only [Dv, D_d, Derivation.map_smul]

variable [IsLocalRing R] {c}

lemma coeff_tau_d (β : Fin n →₀ ℕ) (i : Fin n) (f : R) :
    coeff β (c.tau (c.d i f)) = ((β i + 1 : ℕ) : ℚ) • coeff (β + Finsupp.single i 1) (c.tau f) := by
  rw [coeff_tau, coeff_tau, Dv_d, d_Dv, map_rat_smul]

/-- **Rational weighted duality.** -/
theorem IsCentred.mem_RF_iff [IsNoetherianRing R] (hc : c.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) (t : ℚ) (f : R) :
    f ∈ c.RF e t ↔ ∀ β : Fin n →₀ ℕ, lam e β < t → coeff β (c.tau f) = 0 := by
  obtain ⟨d, w, hd, hw⟩ := exists_scale he
  rw [c.RF_eq_F hd hw, hc.mem_F_iff]
  have hlam : ∀ α : Fin n →₀ ℕ, (Finsupp.weight w α : ℚ) = d * lam e α := by
    intro α
    rw [Finsupp.weight_eq_sum, lam, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Nat.cast_mul, hw i]; ring
  refine forall_congr' fun β => imp_congr_left ?_
  rw [Nat.lt_ceil, hlam]
  constructor
  · intro h; exact lt_of_mul_lt_mul_left h (Nat.cast_nonneg _)
  · intro h; exact mul_lt_mul_of_pos_left h (by exact_mod_cast hd)

lemma IsCentred.RF_le_maximalIdeal (hc : c.IsCentred) {e : Fin n → ℚ} {t : ℚ} (ht : 0 < t) :
    c.RF e t ≤ maximalIdeal R := by
  rw [RF, Ideal.span_le]
  rintro _ ⟨α, -, hα, rfl⟩
  have hα0 : α ≠ 0 := by rintro rfl; rw [lam_zero] at hα; linarith
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra h; push Not at h; exact hα0 (Finsupp.ext h)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (hc.x_mem i) _ (Nat.pos_of_ne_zero hi))

/-- The chart derivations lower the weighted order by their weight. -/
lemma IsCentred.d_mem_RF [IsNoetherianRing R] (hc : c.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) (m : Fin n) {t : ℚ} {f : R} (hf : f ∈ c.RF e t) :
    c.d m f ∈ c.RF e (t - e m) := by
  rw [hc.mem_RF_iff he] at hf ⊢
  intro β hβ
  rw [coeff_tau_d, hf _ (by rw [lam_add, lam_single]; push_cast; linarith)]
  simp

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

namespace Chart

/-- `δ` lowers the `e`-weighted order (with respect to the chart `c`) by at most `s`. -/
def LowersBy (c : Chart R n) (e : Fin n → ℚ) (δ : Derivation ℚ R R) (s : ℚ) : Prop :=
  ∀ t, ∀ f ∈ c.RF e t, δ f ∈ c.RF e (t - s)

lemma one_mem_RF_zero (c : Chart R n) (e : Fin n → ℚ) : (1 : R) ∈ c.RF e 0 :=
  Ideal.subset_span ⟨0, fun _ _ => rfl, by rw [lam_zero], by simp⟩

lemma prod_mem_RF (c : Chart R n) (e : Fin n → ℚ) (s : Finset (Fin n)) (g : Fin n → R)
    (u : Fin n → ℚ) (hg : ∀ i ∈ s, g i ∈ c.RF e (u i)) :
    ∏ i ∈ s, g i ∈ c.RF e (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]; exact c.one_mem_RF_zero e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact c.RF_mul_le e _ _ (Ideal.mul_mem_mul (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi)))

lemma pow_mem_RF (c : Chart R n) (e : Fin n → ℚ) {g : R} {u : ℚ} (hg : g ∈ c.RF e u) (k : ℕ) :
    g ^ k ∈ c.RF e (k * u) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]; exact c.one_mem_RF_zero e
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact c.RF_mul_le e _ _ (Ideal.mul_mem_mul ih hg)

/-- **Monomial criterion.** If the functions of `c'` have the right weighted orders for `c`, the
weighted ideals of `c'` are contained in those of `c`. -/
theorem RF_le_of_x_mem (c c' : Chart R n) {e : Fin n → ℚ}
    (hx : ∀ i, e i ≠ 0 → c'.x i ∈ c.RF e (e i)) (t : ℚ) : c'.RF e t ≤ c.RF e t := by
  rw [RF, Ideal.span_le]
  rintro _ ⟨α, h0, ht, rfl⟩
  refine c.RF_antitone e ht ?_
  have := c.prod_mem_RF e Finset.univ (fun i => c'.x i ^ α i) (fun i => α i * e i) fun i _ => by
    by_cases hi : e i = 0
    · rw [h0 i hi, pow_zero, hi, mul_zero]; exact c.one_mem_RF_zero e
    · exact c.pow_mem_RF e (hx i hi) _
  simpa [lam] using this

variable [IsLocalRing R] {c c' : Chart R n}

/-- **Compatibility criterion.** If the derivations of a centred chart `c'` lower the weighted
order of `c` by at most the weights, then the weighted ideals of `c` are contained in those of
`c'`. -/
theorem IsCentred.RF_le_of_lowersBy [IsNoetherianRing R] (hc : c.IsCentred)
    (hc' : c'.IsCentred) {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i)
    (hdeg : ∀ m, c.LowersBy e (c'.d m) (e m)) (t : ℚ) : c.RF e t ≤ c'.RF e t := by
  intro f hf
  rw [hc'.mem_RF_iff he]
  intro β hβ
  have key : ∀ β, c'.D β f ∈ c.RF e (t - lam e β) := by
    refine Finsupp.induction_single ?_ fun β i ih => ?_
    · rw [D_zero, lam_zero, sub_zero]; exact hf
    · rw [D_add_single, lam_add, lam_single, Nat.cast_one, one_mul, ← sub_sub]
      exact hdeg i _ _ ih
  rw [coeff_tau_eq_zero_iff, Dv, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (hc.RF_le_maximalIdeal (by linarith) (key β))

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

namespace Chart

variable (c : Chart R n)

/-- Reindexing a chart by a permutation. -/
def reindex (σ : Equiv.Perm (Fin n)) : Chart R n where
  x i := c.x (σ i)
  d i := c.d (σ i)
  d_x i j := by rw [c.d_x]; simp [σ.injective.eq_iff]
  span := by
    rw [← c.span]; congr 1
    ext ω; constructor
    · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, by simp⟩

@[simp] lemma reindex_x (σ : Equiv.Perm (Fin n)) (i : Fin n) : (c.reindex σ).x i = c.x (σ i) := rfl
@[simp] lemma reindex_d (σ : Equiv.Perm (Fin n)) (i : Fin n) : (c.reindex σ).d i = c.d (σ i) := rfl

/-- Replacing the `m`-th chart function by `g`, where `∂ₘ g` is a unit. -/
def replace (m : Fin n) (g : R) (u : Rˣ) (hu : c.d m g = u) : Chart R n where
  x := Function.update c.x m g
  d i := if i = m then (↑u⁻¹ : R) • c.d m else c.d i - (↑u⁻¹ * c.d i g) • c.d m
  d_x i j := by
    by_cases hi : i = m
    · subst hi
      rw [ite_eq_left rfl, Derivation.smul_apply, smul_eq_mul]
      by_cases hj : j = i
      · subst hj; rw [Function.update_self, hu, Units.inv_mul, ite_eq_left rfl]
      · rw [Function.update_of_ne hj, c.d_x_ne (Ne.symm hj), mul_zero, ite_eq_right (Ne.symm hj)]
    · rw [ite_eq_right hi, Derivation.coe_sub, Pi.sub_apply, Derivation.smul_apply, smul_eq_mul]
      by_cases hj : j = m
      · subst hj
        rw [Function.update_self, hu, mul_assoc, mul_comm (c.d i g), ← mul_assoc, Units.inv_mul,
          one_mul, sub_self, ite_eq_right hi]
      · rw [Function.update_of_ne hj, c.d_x_ne (Ne.symm hj), mul_zero, sub_zero, c.d_x]
  span := by
    rw [eq_top_iff, ← c.span, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = m
    · subst hj
      -- `dxₘ = u⁻¹ (dg - ∑_{i ≠ m} (∂ᵢ g) dxᵢ)`
      have h := c.kD_eq_sum g
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hu] at h
      have : KaehlerDifferential.D ℚ R (c.x j) = (↑u⁻¹ : R) • (KaehlerDifferential.D ℚ R g -
          ∑ i ∈ Finset.univ.erase j, c.d i g • KaehlerDifferential.D ℚ R (c.x i)) := by
        rw [h, add_sub_cancel_right, smul_smul, Units.inv_mul, one_smul]
      change KaehlerDifferential.D ℚ R (c.x j) ∈ _
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨j, by simp⟩)
        (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i, ?_⟩)))
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    · exact Submodule.subset_span ⟨j, by simp [Function.update_of_ne hj]⟩

lemma replace_x_self (m : Fin n) (g : R) (u : Rˣ) (hu : c.d m g = u) :
    (c.replace m g u hu).x m = g := by simp [replace]

lemma replace_x_ne (m : Fin n) (g : R) (u : Rˣ) (hu : c.d m g = u) {i : Fin n} (hi : i ≠ m) :
    (c.replace m g u hu).x i = c.x i := by simp [replace, Function.update_of_ne hi]

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

namespace Chart

variable (c : Chart R n)

lemma Dv_single_one (l : Fin n) (f : R) : c.Dv (Finsupp.single l 1) f = c.d l f := by
  have := c.d_Dv 0 l f
  rw [Dv_zero, zero_add, Finsupp.coe_zero, Pi.zero_apply] at this
  simpa using this.symm

variable [IsLocalRing R] {c}

lemma IsCentred.reindex (hc : c.IsCentred) (σ : Equiv.Perm (Fin n)) : (c.reindex σ).IsCentred := by
  rw [IsCentred, hc]; congr 1
  ext f; constructor
  · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, by simp⟩
  · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩

lemma IsCentred.RF_one_two_le (hc : c.IsCentred) :
    c.RF (fun _ => 1) 2 ≤ maximalIdeal R ^ 2 := by
  rw [RF, Ideal.span_le]
  rintro _ ⟨α, -, hα, rfl⟩
  have hdeg : 2 ≤ α.degree := by
    have : lam (fun _ => (1 : ℚ)) α = α.degree := by
      simp [lam, Finsupp.degree_eq_sum]
    rw [this] at hα; exact_mod_cast hα
  have hmem : ∏ i, c.x i ^ α i ∈ maximalIdeal R ^ α.degree := by
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hc.x_mem i) _
  exact Ideal.pow_le_pow_right hdeg hmem

/-- Replacing a chart function by an element of `𝔪` with unit derivative keeps the chart centred. -/
lemma IsCentred.replace [IsNoetherianRing R] (hc : c.IsCentred) (m : Fin n) (g : R) (u : Rˣ)
    (hu : c.d m g = u) (hg : g ∈ maximalIdeal R) : (c.replace m g u hu).IsCentred := by
  set c' := c.replace m g u hu
  have hx' : ∀ i, c'.x i ∈ maximalIdeal R := by
    intro i
    by_cases hi : i = m
    · subst hi; rw [c.replace_x_self]; exact hg
    · rw [c.replace_x_ne _ _ _ _ hi]; exact hc.x_mem i
  -- `h = g - ∑ (∂ᵢ g) xᵢ ∈ 𝔪²`
  set h := g - ∑ i, c.d i g * c.x i with hh
  have h2 : h ∈ maximalIdeal R ^ 2 := by
    refine hc.RF_one_two_le ((hc.mem_RF_iff (fun _ => zero_le_one) 2 h).2 fun β hβ => ?_)
    have hdeg : β.degree < 2 := by
      have : lam (fun _ => (1 : ℚ)) β = β.degree := by simp [lam, Finsupp.degree_eq_sum]
      rw [this] at hβ; exact_mod_cast hβ
    rw [coeff_tau_eq_zero_iff]
    by_cases h0 : β = 0
    · subst h0
      rw [Dv_zero, hh]
      refine sub_mem hg (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hc.x_mem i))
    · obtain ⟨l, hl⟩ : ∃ l, β = Finsupp.single l 1 := by
        obtain ⟨l, hl⟩ : ∃ l, β l ≠ 0 := by
          by_contra hc'; push Not at hc'; exact h0 (Finsupp.ext hc')
        refine ⟨l, ?_⟩
        have hsum := hdeg
        rw [Finsupp.degree_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at hsum
        have hrest : ∑ i ∈ Finset.univ.erase l, β i = 0 := by omega
        rw [Finset.sum_eq_zero_iff] at hrest
        ext i
        by_cases hi : i = l
        · subst hi; simp only [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hi)]
          exact hrest i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
      subst hl
      rw [Dv_single_one, hh, map_sub, map_sum]
      have : ∀ i, c.d l (c.d i g * c.x i) =
          (if l = i then c.d i g else 0) + c.x i * c.d l (c.d i g) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, c.d_x, mul_ite, mul_one, mul_zero]
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [sub_add_cancel_left]
      exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hc.x_mem i))
  refine le_antisymm ?_ ((Ideal.span_le).2 (by rintro _ ⟨i, rfl⟩; exact hx' i))
  have hfg : (maximalIdeal R).FG := by
    classical
    rw [hc]; exact ⟨Finset.univ.image c.x, by simp⟩
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (maximalIdeal_le_jacobson _) ?_
  conv_lhs => rw [hc]
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  by_cases hj : j = m
  · subst hj
    have hsplit : ∑ i, c.d i g * c.x i =
        ↑u * c.x j + ∑ i ∈ Finset.univ.erase j, c.d i g * c.x i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hu]
    have hxm : c.x j = ↑u⁻¹ * (g - h - ∑ i ∈ Finset.univ.erase j, c.d i g * c.x i) := by
      have : g - h = ∑ i, c.d i g * c.x i := by rw [hh]; ring
      rw [this, hsplit, add_sub_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hxm]
    refine Ideal.mul_mem_left _ _ (sub_mem (sub_mem ?_ ?_) ?_)
    · exact Submodule.mem_sup_left (Ideal.subset_span ⟨j, c.replace_x_self _ _ _ _⟩)
    · exact Submodule.mem_sup_right (by rw [smul_eq_mul, ← pow_two]; exact h2)
    · refine Submodule.mem_sup_left (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ ?_)
      exact Ideal.subset_span ⟨i, c.replace_x_ne _ _ _ _ (Finset.ne_of_mem_erase hi)⟩
  · exact Submodule.mem_sup_left (Ideal.subset_span ⟨j, c.replace_x_ne _ _ _ _ hj⟩)

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

namespace Chart

/-- The weighted ideals only depend on the chart functions with nonzero weight. -/
lemma RF_congr {c c' : Chart R n} {e : Fin n → ℚ} (h : ∀ i, e i ≠ 0 → c.x i = c'.x i) (t : ℚ) :
    c.RF e t = c'.RF e t := by
  rw [RF, RF]; congr 1
  ext f
  refine exists_congr fun α => and_congr_right fun h0 => and_congr_right fun _ => ?_
  rw [show (∏ i, c.x i ^ α i) = ∏ i, c'.x i ^ α i from Finset.prod_congr rfl fun i _ => by
    by_cases hi : e i = 0
    · rw [h0 i hi, pow_zero, pow_zero]
    · rw [h i hi]]

/-- Larger weights give larger weighted ideals. -/
lemma RF_mono_e (c : Chart R n) {e e' : Fin n → ℚ} (_he : ∀ i, 0 ≤ e i) (hle : ∀ i, e i ≤ e' i)
    (hsupp : ∀ i, e i ≠ 0 → e' i ≠ 0) (t : ℚ) : c.RF e t ≤ c.RF e' t := by
  refine Ideal.span_mono ?_
  rintro _ ⟨α, h0, ht, rfl⟩
  refine ⟨α, fun i hi => h0 i (by by_contra h; exact hsupp i h hi), ht.trans ?_, rfl⟩
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (Nat.cast_nonneg _)

lemma ext' {c c' : Chart R n} (h1 : c.x = c'.x) (h2 : c.d = c'.d) : c = c' := by
  cases c; cases c'; simp only at h1 h2; subst h1; subst h2; rfl

lemma reindex_reindex_symm (c : Chart R n) (σ : Equiv.Perm (Fin n)) :
    (c.reindex σ).reindex σ.symm = c :=
  ext' (funext fun i => by simp) (funext fun i => by simp)

lemma RF_reindex_le (c : Chart R n) {e : Fin n → ℚ} (τ : Equiv.Perm (Fin n))
    (hτ : ∀ i, e (τ i) = e i) (t : ℚ) : (c.reindex τ).RF e t ≤ c.RF e t := by
  rw [RF, Ideal.span_le]
  rintro _ ⟨α, h0, ht, rfl⟩
  refine Ideal.subset_span ⟨Finsupp.equivMapDomain τ α, fun k hk => ?_, ?_, ?_⟩
  · rw [Finsupp.equivMapDomain_apply]
    refine h0 _ ?_
    have := hτ (τ.symm k); rw [Equiv.apply_symm_apply] at this; rw [← this]; exact hk
  · refine ht.trans (le_of_eq ?_)
    simp only [lam, Finsupp.equivMapDomain_apply]
    rw [← Equiv.sum_comp τ (fun i => (α (τ.symm i) : ℚ) * e i)]
    simp only [Equiv.symm_apply_apply, hτ]
  · simp only [reindex_x]
    rw [← Equiv.prod_comp τ (fun k => c.x k ^ (Finsupp.equivMapDomain τ α) k)]
    simp only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

/-- Reindexing by a permutation preserving the weights preserves the weighted ideals. -/
lemma RF_reindex (c : Chart R n) {e : Fin n → ℚ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, e (σ i) = e i)
    (t : ℚ) : (c.reindex σ).RF e t = c.RF e t := by
  refine le_antisymm (c.RF_reindex_le σ hσ t) ?_
  calc c.RF e t = ((c.reindex σ).reindex σ.symm).RF e t := by rw [reindex_reindex_symm]
    _ ≤ (c.reindex σ).RF e t :=
      (c.reindex σ).RF_reindex_le σ.symm (fun i => by rw [← hσ (σ.symm i), Equiv.apply_symm_apply]) t

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

namespace Chart

/-- Iterated lowering. -/
lemma D_mem_RF_of_lowersBy (c c' : Chart R n) (e s : Fin n → ℚ)
    (h : ∀ i, c.LowersBy e (c'.d i) (s i)) :
    ∀ (β : Fin n →₀ ℕ) (t : ℚ) (f : R), f ∈ c.RF e t → c'.D β f ∈ c.RF e (t - lam s β) := by
  refine Finsupp.induction_single ?_ fun β i ih => ?_
  · intro t f hf; rw [D_zero, lam_zero, sub_zero]; exact hf
  · intro t f hf
    rw [D_add_single, lam_add, lam_single, Nat.cast_one, one_mul, ← sub_sub]
    exact h i _ _ (ih t f hf)

lemma Dv_mem_RF_of_lowersBy (c c' : Chart R n) (e s : Fin n → ℚ)
    (h : ∀ i, c.LowersBy e (c'.d i) (s i)) (β : Fin n →₀ ℕ) {t : ℚ} {f : R}
    (hf : f ∈ c.RF e t) : c'.Dv β f ∈ c.RF e (t - lam s β) := by
  rw [Dv, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (D_mem_RF_of_lowersBy c c' e s h β t f hf)

variable [IsLocalRing R] [IsNoetherianRing R]

/-- **Replacement lemma.** Replacing the `m`-th function of a centred chart by an element of the
right weighted order with unit `∂ₘ`-derivative does not change the weighted ideals. -/
theorem IsCentred.RF_replace {c : Chart R n} (hc : c.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) (m : Fin n) (g : R) (u : Rˣ) (hu : c.d m g = u)
    (hg : g ∈ maximalIdeal R) (hgm : g ∈ c.RF e (e m)) (t : ℚ) :
    (c.replace m g u hu).RF e t = c.RF e t := by
  have hc' := hc.replace m g u hu hg
  refine le_antisymm (RF_le_of_x_mem c _ (fun i _ => ?_) t) (hc.RF_le_of_lowersBy hc' he ?_ t)
  · by_cases hi : i = m
    · subst hi; rw [c.replace_x_self]; exact hgm
    · rw [c.replace_x_ne _ _ _ _ hi]; exact c.x_mem_RF e i ‹_›
  · intro i t' f hf
    change (if i = m then (↑u⁻¹ : R) • c.d m else c.d i - (↑u⁻¹ * c.d i g) • c.d m) f ∈ _
    split_ifs with hi
    · subst hi
      rw [Derivation.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_left _ _ (hc.d_mem_RF he i hf)
    · rw [Derivation.coe_sub, Pi.sub_apply, Derivation.smul_apply, smul_eq_mul]
      refine sub_mem (hc.d_mem_RF he i hf) ?_
      rw [mul_assoc]
      refine Ideal.mul_mem_left _ _ ?_
      have h1 := hc.d_mem_RF he i hgm
      have h2 := hc.d_mem_RF he m hf
      have := c.RF_mul_le e _ _ (Ideal.mul_mem_mul h1 h2)
      rwa [show e m - e i + (t' - e m) = t' - e i by ring] at this

/-- Chain rule bound for lowering: `∂ᵢ = ∑ₘ (∂ᵢ x''ₘ) ∂''ₘ`. -/
theorem IsCentred.lowersBy_of_coeff {c'' : Chart R n} (hc'' : c''.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) (δ : Derivation ℚ R R) {s : ℚ}
    (hs : ∀ m, δ (c''.x m) ≠ 0 → e m ≤ s) : c''.LowersBy e δ s := by
  intro t f hf
  rw [c''.eq_sum δ, Derivation.sum_apply']
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [Derivation.smul_apply, smul_eq_mul]
  by_cases hm : δ (c''.x m) = 0
  · rw [hm, zero_mul]; exact zero_mem _
  · exact Ideal.mul_mem_left _ _ (c''.RF_antitone e (by linarith [hs m hm])
      (hc''.d_mem_RF he m hf))

/-- **Fundamental chain rule lemma**, part 1: for `i < j`, `∂ᵢ` of a chart sharing the first `j`
functions with `c''` lowers the weighted order of `c''` by at most `eᵢ`. -/
theorem IsCentred.lowersBy_lt {c c'' : Chart R n} (hc'' : c''.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) {j : ℕ}
    (hagree : ∀ i : Fin n, (i : ℕ) < j → c.x i = c''.x i) (i : Fin n) (hi : (i : ℕ) < j) :
    c''.LowersBy e (c.d i) (e i) := by
  refine hc''.lowersBy_of_coeff he _ fun m hm => ?_
  by_cases hmj : (m : ℕ) < j
  · rw [← hagree m hmj, c.d_x] at hm
    split_ifs at hm with him
    · rw [him]
    · exact absurd rfl hm
  · exact hanti (show i ≤ m from by rw [Fin.le_def]; omega)

/-- **Fundamental chain rule lemma**, part 2: for `i ≥ j`, `∂ᵢ` lowers the weighted order of `c''`
by at most `b` if all weights beyond `j` are `≤ b`. -/
theorem IsCentred.lowersBy_ge {c c'' : Chart R n} (hc'' : c''.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) {j : ℕ} (hagree : ∀ i : Fin n, (i : ℕ) < j → c.x i = c''.x i)
    (i : Fin n) (hi : j ≤ (i : ℕ)) {b : ℚ} (hb : ∀ m : Fin n, j ≤ (m : ℕ) → e m ≤ b) :
    c''.LowersBy e (c.d i) b := by
  refine hc''.lowersBy_of_coeff he _ fun m hm => ?_
  by_cases hmj : (m : ℕ) < j
  · rw [← hagree m hmj, c.d_x, ite_eq_right (by rintro rfl; omega)] at hm
    exact absurd rfl hm
  · exact hb m (by omega)

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

/-- The `b`-completion of weights supported on the first `j` coordinates. -/
def compl (e : Fin n → ℚ) (j : ℕ) (b : ℚ) : Fin n → ℚ := fun i => if (i : ℕ) < j then e i else b

/-- `N(β) = ∑_{i ≥ j} βᵢ`. -/
def tailSum (j : ℕ) (β : Fin n →₀ ℕ) : ℕ := ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), β i

lemma lam_compl {e : Fin n → ℚ} {j : ℕ} (hj : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0) (b : ℚ)
    (β : Fin n →₀ ℕ) : lam (compl e j b) β = lam e β + b * tailSum j β := by
  simp only [lam, compl, tailSum, Nat.cast_sum, Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j)]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < j), (β i : ℚ) * e i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_filter] at hi; rw [hj i (by omega), mul_zero]
  rw [h1, add_zero]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by rw [Finset.mem_filter] at hi; rw [ite_eq_left hi.2]
  · rw [show Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < j) =
        Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)) from by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]]
    exact Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_filter] at hi; rw [ite_eq_right (by omega)]; ring

namespace Chart

variable [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
lemma IsCentred.maximalIdeal_le_RF {c : Chart R n} (hc : c.IsCentred) {e : Fin n → ℚ} {b : ℚ}
    (hb : ∀ i, e i ≠ 0 ∧ b ≤ e i) : maximalIdeal R ≤ c.RF e b := by
  rw [hc, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact c.RF_antitone e (hb i).2 (c.x_mem_RF e i (hb i).1)

omit [IsNoetherianRing R] in
/-- **Completion independence.** -/
theorem IsCentred.RF_compl_eq {c c' : Chart R n} (hc : c.IsCentred) (hc' : c'.IsCentred)
    {e : Fin n → ℚ} {j : ℕ} {b : ℚ} (hb0 : 0 < b) (hbe : ∀ i : Fin n, (i : ℕ) < j → b ≤ e i)
    (hagree : ∀ i : Fin n, (i : ℕ) < j → c.x i = c'.x i) (t : ℚ) :
    c.RF (compl e j b) t = c'.RF (compl e j b) t := by
  have hall : ∀ i, compl e j b i ≠ 0 ∧ b ≤ compl e j b i := fun i => by
    simp only [compl]; split_ifs with h
    · exact ⟨(lt_of_lt_of_le hb0 (hbe i h)).ne', hbe i h⟩
    · exact ⟨hb0.ne', le_rfl⟩
  have key : ∀ (c c' : Chart R n), c'.IsCentred →
      (∀ i : Fin n, (i : ℕ) < j → c.x i = c'.x i) → c.IsCentred →
      c.RF (compl e j b) t ≤ c'.RF (compl e j b) t := by
    intro c c' hc' hag hc
    refine RF_le_of_x_mem c' c (fun i hi => ?_) t
    by_cases hij : (i : ℕ) < j
    · rw [hag i hij]; exact c'.x_mem_RF _ i hi
    · have hle : b ≤ compl e j b i := (hall i).2
      have hx := hc.x_mem i
      exact hc'.maximalIdeal_le_RF hall |>.trans (c'.RF_antitone _ (by
        simp only [compl, ite_eq_right hij]; exact le_rfl)) hx
  exact le_antisymm (key c c' hc' hagree hc) (key c' c hc (fun i hi => (hagree i hi).symm) hc')

end Chart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

variable {n : ℕ}

/-- `Ξ(β) = N(β) / (1 - λ_e(β))`. -/
def Xi (e : Fin n → ℚ) (j : ℕ) (β : Fin n →₀ ℕ) : ℚ := (tailSum j β : ℚ) / (1 - lam e β)

lemma exists_min_Xi {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (j : ℕ) (S : Set (Fin n →₀ ℕ))
    (hS : S.Nonempty) (hlt : ∀ β ∈ S, lam e β < 1) :
    ∃ β ∈ S, ∀ β' ∈ S, Xi e j β ≤ Xi e j β' := by
  classical
  obtain ⟨d, w, hd, hw⟩ := Chart.exists_scale he
  have hlam : ∀ α : Fin n →₀ ℕ, (Finsupp.weight w α : ℚ) = d * lam e α := by
    intro α
    rw [Finsupp.weight_eq_sum, lam, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Nat.cast_mul, hw i]; ring
  have hW : ∀ β ∈ S, Finsupp.weight w β < d := by
    intro β hβ
    have := hlam β
    have h1 := hlt β hβ
    have : (Finsupp.weight w β : ℚ) < d := by
      rw [this]; nlinarith [show (0 : ℚ) < d from by exact_mod_cast hd]
    exact_mod_cast this
  let K : (Fin n →₀ ℕ) → ℕ := fun β =>
    tailSum j β * d * (d.factorial / (d - Finsupp.weight w β))
  have hK : ∀ β ∈ S, Xi e j β = (K β : ℚ) / d.factorial := by
    intro β hβ
    have hWd := hW β hβ
    have hdvd : d - Finsupp.weight w β ∣ d.factorial :=
      Nat.dvd_factorial (by omega) (Nat.sub_le _ _)
    have hpos : (0 : ℚ) < (d - Finsupp.weight w β : ℕ) := by exact_mod_cast (by omega : 0 < _)
    have hfact : (0 : ℚ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
    simp only [K, Xi]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_div hdvd hpos.ne']
    have h1 : 1 - lam e β = ((d - Finsupp.weight w β : ℕ) : ℚ) / d := by
      rw [Nat.cast_sub hWd.le, hlam]
      field_simp
    rw [h1]
    field_simp
  have hex : ∃ k, ∃ β ∈ S, K β = k := by
    obtain ⟨β, hβ⟩ := hS; exact ⟨_, β, hβ, rfl⟩
  obtain ⟨β₀, hβ₀, hk⟩ := Nat.find_spec hex
  refine ⟨β₀, hβ₀, fun β' hβ' => ?_⟩
  rw [hK β₀ hβ₀, hK β' hβ']
  have : K β₀ ≤ K β' := hk ▸ Nat.find_min' hex ⟨β', hβ', rfl⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast this) (by positivity)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ}

/-- A *marked centre* at the closed point of `R`: a centred chart and antitone nonnegative weights
`e` (the centre is `(x₀^{1/e₀}, x₁^{1/e₁}, …)` over the coordinates with `eᵢ ≠ 0`). -/
structure MC (R : Type*) [CommRing R] [Algebra ℚ R] [IsLocalRing R] (n : ℕ) where
  c : Chart R n
  e : Fin n → ℚ
  centred : c.IsCentred
  nonneg : ∀ i, 0 ≤ e i
  anti : Antitone e

namespace MC

/-- The weighted ideals of a marked centre. -/
def RF (J : MC R n) (t : ℚ) : Ideal R := J.c.RF J.e t

/-- Admissibility for an ideal: `v_J(I) ≥ 1`. -/
def Adm (I : Ideal R) (J : MC R n) : Prop := I ≤ J.RF 1

/-- `J` is `j`-semi-associated to `I` (Brais, Def. 3.1.6), in terms of the weights `e`
(a larger invariant corresponds to lexicographically smaller weights). -/
structure SA (I : Ideal R) (j : ℕ) (J : MC R n) : Prop where
  supp : ∀ i : Fin n, J.e i ≠ 0 ↔ (i : ℕ) < j
  dom0 : ∃ J' : MC R n, J'.Adm I ∧ ∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i
  max : ∀ J' : MC R n, J'.Adm I → ∀ i : Fin n, (i : ℕ) < j →
    (∀ i' : Fin n, i' < i → J'.e i' = J.e i') → J.e i ≤ J'.e i
  dom : ∀ J' : MC R n, J'.Adm I → (∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) →
    ∃ c'' : Chart R n, c''.IsCentred ∧ (∀ t, c''.RF J'.e t = J'.RF t) ∧
      ∀ i : Fin n, (i : ℕ) < j → c''.x i = J.c.x i

end MC

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

namespace MC

variable {I : Ideal R} {j : ℕ} {J : MC R n}

omit [IsNoetherianRing R] in
lemma SA.e_eq_zero (hSA : SA I j J) {i : Fin n} (hi : j ≤ (i : ℕ)) : J.e i = 0 := by
  by_contra h; exact absurd ((hSA.supp i).1 h) (by omega)

omit [IsNoetherianRing R] in
lemma SA.e_pos (hSA : SA I j J) {i : Fin n} (hi : (i : ℕ) < j) : 0 < J.e i :=
  lt_of_le_of_ne (J.nonneg i) (Ne.symm ((hSA.supp i).2 hi))

omit [IsNoetherianRing R] in
/-- An admissible centre with the same weights as a semi-associated one makes it admissible. -/
lemma SA.adm_of_agree (hSA : SA I j J) (J' : MC R n) (hJ' : J'.Adm I)
    (hag : ∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i)
    (hz : ∀ i : Fin n, j ≤ (i : ℕ) → J'.e i = 0) : J.Adm I := by
  have he : J'.e = J.e := funext fun i => by
    by_cases hi : (i : ℕ) < j
    · exact hag i hi
    · rw [hz i (by omega), hSA.e_eq_zero (by omega)]
  obtain ⟨c'', -, hRF, hx⟩ := hSA.dom J' hJ' hag
  have : J.RF 1 = J'.RF 1 := by
    rw [← hRF, he, RF]
    exact Chart.RF_congr (fun i hi => (hx i ((hSA.supp i).1 hi)).symm) 1
  rw [Adm, this]; exact hJ'

omit [IsNoetherianRing R] in
/-- If `J` is semi-associated and not admissible, an admissible centre agreeing on the first `j`
weights has a positive `j`-th weight. -/
lemma SA.next_pos (hSA : SA I j J) (hna : ¬ J.Adm I) (J' : MC R n) (hJ' : J'.Adm I)
    (hag : ∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) :
    ∃ hj : j < n, 0 < J'.e ⟨j, hj⟩ := by
  by_contra h
  push Not at h
  refine hna (hSA.adm_of_agree J' hJ' hag fun i hi => ?_)
  have hj : j < n := lt_of_le_of_lt hi i.2
  have h0 : J'.e ⟨j, hj⟩ = 0 := le_antisymm (h hj) (J'.nonneg _)
  exact le_antisymm (h0 ▸ J'.anti (show (⟨j, hj⟩ : Fin n) ≤ i from hi)) (J'.nonneg i)

omit [IsNoetherianRing R] in
/-- The completion `compl J.e j b` with the `j`-th weight of an admissible centre agreeing with `J`
on the first `j` weights is admissible. -/
lemma SA.compl_adm (hSA : SA I j J) (J' : MC R n) (hJ' : J'.Adm I)
    (hag : ∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) (hj : j < n) (hb : 0 < J'.e ⟨j, hj⟩) :
    I ≤ J.c.RF (compl J.e j (J'.e ⟨j, hj⟩)) 1 := by
  set b := J'.e ⟨j, hj⟩
  obtain ⟨c'', hc'', hRF, hx⟩ := hSA.dom J' hJ' hag
  have hbe : ∀ i : Fin n, (i : ℕ) < j → b ≤ J.e i := fun i hi => by
    rw [← hag i hi]; exact J'.anti (show i ≤ ⟨j, hj⟩ from Fin.le_def.2 (by simp only; omega))
  have h1 : J'.RF 1 ≤ c''.RF (compl J.e j b) 1 := by
    rw [← hRF]
    refine c''.RF_mono_e J'.nonneg (fun i => ?_) (fun i _ => ?_) 1
    · simp only [compl]; split_ifs with hi
      · rw [hag i hi]
      · exact J'.anti (show (⟨j, hj⟩ : Fin n) ≤ i from Fin.le_def.2 (by simp only; omega))
    · simp only [compl]; split_ifs with hi
      · exact (hSA.e_pos hi).ne'
      · exact hb.ne'
  rw [Chart.IsCentred.RF_compl_eq hc'' J.centred hb hbe (fun i hi => hx i hi) 1] at h1
  exact hJ'.trans h1

end MC

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

namespace MC

variable {I : Ideal R} {j : ℕ} {J : MC R n}

lemma tailSum_pos_exists {j : ℕ} {β : Fin n →₀ ℕ} (h : 0 < tailSum j β) :
    ∃ l : Fin n, j ≤ (l : ℕ) ∧ β l ≠ 0 := by
  obtain ⟨l, hl, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  exact ⟨l, (Finset.mem_filter.1 hl).2, hne⟩

lemma tailSum_add (j : ℕ) (α β : Fin n →₀ ℕ) : tailSum j (α + β) = tailSum j α + tailSum j β := by
  simp only [tailSum, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]

lemma tailSum_single {j : ℕ} {l : Fin n} (hl : j ≤ (l : ℕ)) : tailSum j (Finsupp.single l 1) = 1 := by
  simp only [tailSum]
  rw [Finset.sum_eq_single l]
  · simp
  · intro i _ hi; rw [Finsupp.single_apply, ite_eq_right (Ne.symm hi)]
  · intro h; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ l, hl⟩) h

lemma add_single_sub {β : Fin n →₀ ℕ} {l : Fin n} (hβ : β l ≠ 0) :
    (β - Finsupp.single l 1) + Finsupp.single l 1 = β := by
  ext i
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h; omega
  · omega

lemma tailSum_sub_single {j : ℕ} {β : Fin n →₀ ℕ} {l : Fin n} (hl : j ≤ (l : ℕ)) (hβ : β l ≠ 0) :
    tailSum j (β - Finsupp.single l 1) + 1 = tailSum j β := by
  conv_rhs => rw [← add_single_sub hβ]
  rw [tailSum_add, tailSum_single hl]

end MC

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

namespace MC

variable {I : Ideal R} {j : ℕ} {J : MC R n}

/-- Data of the Method-1 step: the next weight `b₊` and a minimizer `βs`. -/
lemma SA.step_data (hSA : SA I j J) (hna : ¬ J.Adm I) :
    ∃ (hj : j < n) (βs : Fin n →₀ ℕ) (f : R), f ∈ I ∧ coeff βs (J.c.tau f) ≠ 0 ∧
      lam J.e βs < 1 ∧ 0 < tailSum j βs ∧
      (∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) → lam J.e β < 1 →
        Xi J.e j βs ≤ Xi J.e j β) ∧
      (∀ J' : MC R n, J'.Adm I → (∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) →
        0 < J'.e ⟨j, hj⟩ ∧ (1 - lam J.e βs) / tailSum j βs ≤ J'.e ⟨j, hj⟩) ∧
      (∀ i : Fin n, (i : ℕ) < j → (1 - lam J.e βs) / tailSum j βs ≤ J.e i) := by
  classical
  obtain ⟨J₀, hJ₀, hag₀⟩ := hSA.dom0
  obtain ⟨hj, hb₀⟩ := hSA.next_pos hna J₀ hJ₀ hag₀
  have hzero : ∀ i : Fin n, j ≤ (i : ℕ) → J.e i = 0 := fun i hi => hSA.e_eq_zero hi
  set S : Set (Fin n →₀ ℕ) := {β | (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) ∧ lam J.e β < 1} with hSdef
  have hS : S.Nonempty := by
    by_contra hS
    apply hna
    intro f hf
    rw [RF, J.centred.mem_RF_iff J.nonneg]
    intro β hβ
    by_contra hne
    exact hS ⟨β, ⟨f, hf, hne⟩, hβ⟩
  -- general bound from admissible completions
  have hbound : ∀ J' : MC R n, J'.Adm I → (∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) →
      ∀ β ∈ S, 1 ≤ lam J.e β + J'.e ⟨j, hj⟩ * tailSum j β := by
    intro J' hJ' hag β hβ
    obtain ⟨hj', hb'⟩ := hSA.next_pos hna J' hJ' hag
    have hc := hSA.compl_adm J' hJ' hag hj hb'
    have hnn : ∀ i, 0 ≤ compl J.e j (J'.e ⟨j, hj⟩) i := fun i => by
      simp only [compl]; split_ifs
      · exact J.nonneg i
      · exact hb'.le
    obtain ⟨⟨g, hg, hne⟩, -⟩ := hβ
    have := (J.centred.mem_RF_iff hnn 1 g).1 (hc hg) β
    rw [← lam_compl hzero]
    by_contra hlt; push Not at hlt
    exact hne (this hlt)
  obtain ⟨βs, hβs, hmin⟩ := exists_min_Xi J.nonneg j S hS (fun β hβ => hβ.2)
  obtain ⟨⟨f, hf, hfne⟩, hlt⟩ := hβs
  have h1 := hbound J₀ hJ₀ hag₀ βs ⟨⟨f, hf, hfne⟩, hlt⟩
  have hN : 0 < tailSum j βs := by
    by_contra h0; push Not at h0
    have : tailSum j βs = 0 := by omega
    rw [this, Nat.cast_zero, mul_zero, add_zero] at h1; linarith
  have hNq : (0 : ℚ) < tailSum j βs := by exact_mod_cast hN
  refine ⟨hj, βs, f, hf, hfne, hlt, hN, fun β hβ hβlt => hmin β ⟨hβ, hβlt⟩, ?_, ?_⟩
  · intro J' hJ' hag
    obtain ⟨hj', hb'⟩ := hSA.next_pos hna J' hJ' hag
    refine ⟨hb', ?_⟩
    have := hbound J' hJ' hag βs ⟨⟨f, hf, hfne⟩, hlt⟩
    rw [div_le_iff₀ hNq]; linarith
  · intro i hi
    have hle : (1 - lam J.e βs) / tailSum j βs ≤ J₀.e ⟨j, hj⟩ := by
      rw [div_le_iff₀ hNq]; linarith
    refine hle.trans ?_
    rw [← hag₀ i hi]
    exact J₀.anti (Fin.le_def.2 (by simp only; omega))

end MC

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

namespace MC

variable {I : Ideal R} {j : ℕ} {J : MC R n}

/-- **Method 1, inductive step** (Brais, Prop. 3.2.7): a non-admissible `j`-semi-associated marked
centre extends to a `(j+1)`-semi-associated one. -/
theorem SA.step (hSA : SA I j J) (hna : ¬ J.Adm I) : ∃ Jp : MC R n, SA I (j + 1) Jp := by
  classical
  obtain ⟨hj, βs, f, hf, hfne, hlt, hN, hmin, hnext, hbJ⟩ := hSA.step_data hna
  set jj : Fin n := ⟨j, hj⟩ with hjj
  set bp : ℚ := (1 - lam J.e βs) / tailSum j βs with hbpdef
  have hNq : (0 : ℚ) < tailSum j βs := by exact_mod_cast hN
  have hbp : 0 < bp := div_pos (by linarith) hNq
  have hzero : ∀ i : Fin n, j ≤ (i : ℕ) → J.e i = 0 := fun i hi => hSA.e_eq_zero hi
  have hkey : lam J.e βs + bp * tailSum j βs = 1 := by
    rw [hbpdef]; field_simp; ring
  have hS_bound : ∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) → lam J.e β < 1 →
      1 ≤ lam J.e β + bp * tailSum j β := by
    intro β hβ hβlt
    have hX := hmin β hβ hβlt
    simp only [Xi] at hX
    have h1 : 0 < 1 - lam J.e β := by linarith
    have h2 : 0 < 1 - lam J.e βs := by linarith
    rw [div_le_div_iff₀ h2 h1] at hX
    have : 1 - lam J.e β ≤ bp * tailSum j β := by
      rw [hbpdef, div_mul_eq_mul_div, le_div_iff₀ hNq]; linarith
    linarith
  -- the completion is an admissible marked centre
  have hc_nonneg : ∀ i, 0 ≤ compl J.e j bp i := fun i => by
    simp only [compl]; split_ifs
    · exact J.nonneg i
    · exact hbp.le
  have hc_anti : Antitone (compl J.e j bp) := by
    intro i i' hii'
    simp only [compl]
    by_cases h1 : (i' : ℕ) < j
    · have h2 : (i : ℕ) < j := lt_of_le_of_lt (Fin.le_def.1 hii') h1
      rw [ite_eq_left h1, ite_eq_left h2]; exact J.anti hii'
    · rw [ite_eq_right h1]
      by_cases h2 : (i : ℕ) < j
      · rw [ite_eq_left h2]; exact hbJ i h2
      · rw [ite_eq_right h2]
  have hc_adm : I ≤ J.c.RF (compl J.e j bp) 1 := by
    intro g hg
    rw [J.centred.mem_RF_iff hc_nonneg]
    intro β hβ
    by_contra hne
    rw [lam_compl hzero] at hβ
    by_cases hβ1 : lam J.e β < 1
    · have := hS_bound β ⟨g, hg, hne⟩ hβ1; linarith
    · have : 0 ≤ bp * tailSum j β := mul_nonneg hbp.le (Nat.cast_nonneg _)
      linarith
  -- the new parameter
  obtain ⟨l, hl, hβl⟩ := tailSum_pos_exists hN
  set γ := βs - Finsupp.single l 1 with hγdef
  have hγ : γ + Finsupp.single l 1 = βs := add_single_sub hβl
  have hlamγ : lam J.e γ = lam J.e βs := by
    rw [← hγ, lam_add, lam_single, hzero l hl, mul_zero, add_zero]
  have htailγ : tailSum j γ + 1 = tailSum j βs := tailSum_sub_single hl hβl
  set xb := J.c.Dv γ f with hxb
  have hdl : J.c.d l xb = ((γ l + 1 : ℕ) : ℚ) • J.c.Dv βs f := by rw [hxb, Chart.d_Dv, hγ]
  have hdl_nm : J.c.d l xb ∉ maximalIdeal R := by
    intro hmem
    rw [hdl, ← residue_eq_zero_iff, map_rat_smul] at hmem
    rw [← Chart.coeff_tau] at hmem
    exact hfne ((smul_eq_zero.1 hmem).resolve_left (by positivity))
  have hxb_mem : xb ∈ maximalIdeal R := by
    rw [hxb, ← residue_eq_zero_iff, ← Chart.coeff_tau]
    by_contra hne
    have hX := hmin γ ⟨f, hf, hne⟩ (by rw [hlamγ]; exact hlt)
    simp only [Xi, hlamγ] at hX
    have h2 : 0 < 1 - lam J.e βs := by linarith
    rw [div_le_div_iff_of_pos_right h2] at hX
    have : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j βs := by exact_mod_cast htailγ
    linarith
  obtain ⟨u, hu⟩ := notMem_maximalIdeal.1 hdl_nm
  -- the new chart and weights
  set cp := (J.c.replace l xb u hu.symm).reindex (Equiv.swap jj l) with hcp
  have hcp_centred : cp.IsCentred := (J.centred.replace l xb u hu.symm hxb_mem).reindex _
  set ep : Fin n → ℚ := fun i => if (i : ℕ) < j then J.e i else if (i : ℕ) = j then bp else 0
    with hep
  have hep_nonneg : ∀ i, 0 ≤ ep i := fun i => by
    simp only [hep]; split_ifs
    · exact J.nonneg i
    · exact hbp.le
    · exact le_rfl
  have hep_anti : Antitone ep := by
    intro i i' hii'
    have hle := Fin.le_def.1 hii'
    simp only [hep]
    by_cases h1 : (i' : ℕ) < j
    · rw [ite_eq_left h1, ite_eq_left (lt_of_le_of_lt hle h1)]; exact J.anti hii'
    · rw [ite_eq_right h1]
      by_cases h2 : (i' : ℕ) = j
      · rw [ite_eq_left h2]
        by_cases h3 : (i : ℕ) < j
        · rw [ite_eq_left h3]; exact hbJ i h3
        · rw [ite_eq_right h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h2]
        split_ifs
        · exact J.nonneg i
        · exact hbp.le
        · exact le_rfl
  have hcp_x_lt : ∀ i : Fin n, (i : ℕ) < j → cp.x i = J.c.x i := by
    intro i hi
    have h1 : i ≠ jj := fun h => by rw [h] at hi; simp [hjj] at hi
    have h2 : i ≠ l := fun h => by rw [h] at hi; omega
    rw [hcp, Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne h1 h2, J.c.replace_x_ne _ _ _ _ h2]
  have hcp_x_j : cp.x jj = xb := by
    rw [hcp, Chart.reindex_x, Equiv.swap_apply_left, J.c.replace_x_self]
  refine ⟨⟨cp, ep, hcp_centred, hep_nonneg, hep_anti⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- support
    intro i
    simp only [hep]
    by_cases h1 : (i : ℕ) < j
    · rw [ite_eq_left h1]; exact ⟨fun _ => by omega, fun _ => (hSA.supp i).2 h1⟩
    · rw [ite_eq_right h1]
      by_cases h2 : (i : ℕ) = j
      · rw [ite_eq_left h2]; exact ⟨fun _ => by omega, fun _ => hbp.ne'⟩
      · rw [ite_eq_right h2]; exact ⟨fun h => absurd rfl h, fun h => by omega⟩
  · -- domination by an admissible centre: the completion
    refine ⟨⟨J.c, compl J.e j bp, J.centred, hc_nonneg, hc_anti⟩, hc_adm, fun i hi => ?_⟩
    show compl J.e j bp i = ep i
    simp only [compl, hep]
    by_cases h1 : (i : ℕ) < j
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left (by omega)]
  · -- maximality
    intro J' hJ' i hi hbelow
    by_cases h1 : (i : ℕ) < j
    · have : ep i = J.e i := by simp only [hep, ite_eq_left h1]
      show ep i ≤ J'.e i
      rw [this]
      refine hSA.max J' hJ' i h1 fun i' hi' => ?_
      rw [hbelow i' hi']
      simp only [hep, ite_eq_left (lt_trans (Fin.lt_def.1 hi') h1)]
    · have hij : (i : ℕ) = j := by omega
      have hieq : i = jj := Fin.ext hij
      subst hieq
      have hag : ∀ i' : Fin n, (i' : ℕ) < j → J'.e i' = J.e i' := fun i' hi' => by
        rw [hbelow i' (Fin.lt_def.2 hi')]
        simp only [hep, ite_eq_left hi']
      have := (hnext J' hJ' hag).2
      show ep jj ≤ J'.e jj
      simp only [hep, ite_eq_right h1, ite_eq_left hij]
      exact this
  · -- domination
    intro J' hJ' hag
    have hag_j : ∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i := fun i hi => by
      rw [hag i (by omega)]; show ep i = J.e i; simp only [hep, ite_eq_left hi]
    have hJ'j : J'.e jj = bp := by
      rw [hag jj (by simp [hjj])]; show ep jj = bp; simp [hep, hjj]
    obtain ⟨c'', hc'', hRF, hx⟩ := hSA.dom J' hJ' hag_j
    have hf' : f ∈ c''.RF J'.e 1 := by rw [hRF]; exact hJ' hf
    -- lowering bounds for the derivations of `J.c` with respect to `(c'', J'.e)`
    have hlow : ∀ i, c''.LowersBy J'.e (J.c.d i) (compl J.e j bp i) := by
      intro i
      by_cases hi : (i : ℕ) < j
      · have := hc''.lowersBy_lt (c := J.c) J'.nonneg J'.anti (fun i' hi' => (hx i' hi').symm) i hi
        simp only [compl, ite_eq_left hi]
        rwa [hag_j i hi] at this
      · simp only [compl, ite_eq_right hi]
        refine hc''.lowersBy_ge (c := J.c) J'.nonneg (fun i' hi' => (hx i' hi').symm) i (by omega)
          fun m hm => ?_
        rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by simp only [hjj, Fin.val_mk]; omega))
    have hxb_RF : xb ∈ c''.RF J'.e bp := by
      have hm1 := Chart.Dv_mem_RF_of_lowersBy c'' J.c J'.e (compl J.e j bp) hlow γ hf'
      rw [lam_compl hzero, hlamγ] at hm1
      have htq : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j βs := by exact_mod_cast htailγ
      have hm2 : 1 - (lam J.e βs + bp * (tailSum j γ : ℚ)) = bp := by
        have := hkey; rw [← htq] at this; linarith
      rw [hm2] at hm1
      exact hm1
    -- a coordinate of `c''` in which `xb` has a linear term
    obtain ⟨m, hm, hmnm⟩ : ∃ m : Fin n, j ≤ (m : ℕ) ∧ c''.d m xb ∉ maximalIdeal R := by
      by_contra hcon
      push Not at hcon
      apply hdl_nm
      rw [c''.eq_sum (J.c.d l), Derivation.sum_apply']
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [Derivation.smul_apply, smul_eq_mul]
      by_cases hmj : (m : ℕ) < j
      · rw [hx m hmj, J.c.d_x, ite_eq_right (fun h => by rw [h] at hl; omega), zero_mul]
        exact zero_mem _
      · exact Ideal.mul_mem_left _ _ (hcon m (by omega))
    have hJ'm : J'.e m = bp := by
      refine le_antisymm ?_ ?_
      · rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by simp only [hjj, Fin.val_mk]; omega))
      · by_contra hlt'
        push Not at hlt'
        have := (hc''.mem_RF_iff J'.nonneg bp xb).1 hxb_RF (Finsupp.single m 1) (by
          rw [lam_single]; simpa using hlt')
        rw [Chart.coeff_tau_eq_zero_iff, Chart.Dv_single_one] at this
        exact hmnm this
    obtain ⟨u', hu'⟩ := notMem_maximalIdeal.1 hmnm
    refine ⟨(c''.replace m xb u' hu'.symm).reindex (Equiv.swap jj m),
      (hc''.replace m xb u' hu'.symm hxb_mem).reindex _, fun t => ?_, fun i hi => ?_⟩
    · rw [Chart.RF_reindex _ _ (fun i => by
          rcases eq_or_ne i jj with h | h
          · rw [h, Equiv.swap_apply_left, hJ'm, hJ'j]
          · rcases eq_or_ne i m with h' | h'
            · rw [h', Equiv.swap_apply_right, hJ'm, hJ'j]
            · rw [Equiv.swap_apply_of_ne_of_ne h h'])]
      rw [hc''.RF_replace J'.nonneg m xb u' hu'.symm hxb_mem (by rw [hJ'm]; exact hxb_RF), hRF]
    · show ((c''.replace m xb u' hu'.symm).reindex (Equiv.swap jj m)).x i = cp.x i
      by_cases hij : (i : ℕ) < j
      · have h1 : i ≠ jj := fun h => by rw [h] at hij; simp [hjj] at hij
        have h2 : i ≠ m := fun h => by rw [h] at hij; omega
        rw [Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne h1 h2, c''.replace_x_ne _ _ _ _ h2,
          hx i hij, hcp_x_lt i hij]
      · have hieq : i = jj := Fin.ext (by simp [hjj]; omega)
        subst hieq
        rw [Chart.reindex_x, Equiv.swap_apply_left, c''.replace_x_self, hcp_x_j]

end MC

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

namespace Chart

variable {c : Chart R n}

omit [IsNoetherianRing R] in
lemma IsCentred.RF_one_le_pow (hc : c.IsCentred) (N : ℕ) :
    c.RF (fun _ => 1) N ≤ maximalIdeal R ^ N := by
  rw [RF, Ideal.span_le]
  rintro _ ⟨α, -, hα, rfl⟩
  have hdeg : N ≤ α.degree := by
    have : lam (fun _ => (1 : ℚ)) α = α.degree := by simp [lam, Finsupp.degree_eq_sum]
    rw [this] at hα; exact_mod_cast hα
  have hmem : ∏ i, c.x i ^ α i ∈ maximalIdeal R ^ α.degree := by
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hc.x_mem i) _
  exact Ideal.pow_le_pow_right hdeg hmem

/-- The residual Taylor map of a centred chart is injective. -/
lemma IsCentred.tau_injective (hc : c.IsCentred) : Function.Injective c.tau := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hmem : ∀ N : ℕ, f ∈ maximalIdeal R ^ N := fun N =>
    hc.RF_one_le_pow N ((hc.mem_RF_iff (fun _ => zero_le_one) N f).2 fun β _ => by rw [hf, map_zero])
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact hmem

end Chart

namespace MC

variable {I : Ideal R}

/-- An admissible centre exists for a nonzero ideal contained in `𝔪`. -/
lemma exists_adm (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal R) (c : Chart R n) (hc : c.IsCentred) :
    ∃ J : MC R n, J.Adm I := by
  classical
  obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hτ : c.tau f ≠ 0 := fun h => hf0 (hc.tau_injective (by rw [h, map_zero]))
  obtain ⟨β, hβ⟩ : ∃ β, coeff β (c.tau f) ≠ 0 := by
    by_contra h; push Not at h; exact hτ (MvPowerSeries.ext fun β => by rw [h β, map_zero])
  have hex : ∃ N : ℕ, ∃ g ∈ I, ∃ β : Fin n →₀ ℕ, coeff β (c.tau g) ≠ 0 ∧ β.degree = N :=
    ⟨_, f, hfI, β, hβ, rfl⟩
  set N := Nat.find hex with hN
  obtain ⟨g, hgI, βg, hβg, hdeg⟩ := Nat.find_spec hex
  have hdeg' : βg.degree = N := hdeg
  have hN1 : 1 ≤ N := by
    by_contra h0
    have : N = 0 := by omega
    rw [this] at hdeg'
    have hdeg := hdeg'
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    subst hdeg
    apply hβg
    rw [coeff_zero_eq_constantCoeff_apply, Chart.constantCoeff_tau, residue_eq_zero_iff]
    exact hIm hgI
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN1
  refine ⟨⟨c, fun _ => 1 / N, hc, fun _ => by positivity, fun _ _ _ => le_rfl⟩, fun h hh => ?_⟩
  rw [RF, hc.mem_RF_iff (fun _ => by positivity)]
  intro β' hβ'
  by_contra hne
  have hlam : lam (fun _ => (1 : ℚ) / N) β' = β'.degree / N := by
    simp only [lam, Finsupp.degree_eq_sum, Nat.cast_sum]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlam, div_lt_one hNq] at hβ'
  have : N ≤ β'.degree := Nat.find_min' hex ⟨h, hh, β', hne, rfl⟩
  have : (N : ℚ) ≤ β'.degree := by exact_mod_cast this
  linarith

/-- The zero centre is `0`-semi-associated. -/
lemma sa_zero (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal R) (c : Chart R n) (hc : c.IsCentred) :
    SA I 0 ⟨c, 0, hc, fun _ => le_rfl, fun _ _ _ => le_rfl⟩ := by
  obtain ⟨J₁, hJ₁⟩ := exists_adm hI hIm c hc
  refine ⟨fun i => by simp, ⟨J₁, hJ₁, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
    fun J' _ i hi => absurd hi (Nat.not_lt_zero _),
    fun J' _ _ => ⟨J'.c, J'.centred, fun _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩

/-- Iterating Method 1 produces an admissible semi-associated centre. -/
lemma exists_sa_adm (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal R) (c : Chart R n) (hc : c.IsCentred) :
    ∃ (k : ℕ) (J : MC R n), SA I k J ∧ J.Adm I := by
  have key : ∀ d j, n - j = d → ∀ J : MC R n, SA I j J →
      ∃ (k : ℕ) (J : MC R n), SA I k J ∧ J.Adm I := by
    intro d
    induction d with
    | zero =>
      intro j hj J hJ
      by_cases ha : J.Adm I
      · exact ⟨j, J, hJ, ha⟩
      · obtain ⟨hjn, -⟩ := hJ.step_data ha
        omega
    | succ d ih =>
      intro j hj J hJ
      by_cases ha : J.Adm I
      · exact ⟨j, J, hJ, ha⟩
      · obtain ⟨Jp, hJp⟩ := hJ.step ha
        exact ih (j + 1) (by omega) Jp hJp
  exact key (n - 0) 0 rfl _ (sa_zero hI hIm c hc)

/-- **Uniqueness of the maximal admissible marked centre** (Abramovich–Temkin–Włodarczyk,
Thm. 5.3.1; Brais, Thm. 3.1.1).  For a nonzero ideal `I ⊆ 𝔪` of a Noetherian local `ℚ`-algebra
with a centred chart, there is an admissible marked centre whose weights are lexicographically
minimal (i.e. whose invariant is maximal), and every admissible marked centre with the same weights
has the same weighted ideals. -/
theorem exists_max (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal R) (c : Chart R n) (hc : c.IsCentred) :
    ∃ J : MC R n, J.Adm I ∧ ∀ J' : MC R n, J'.Adm I →
      toLex J.e ≤ toLex J'.e ∧ (J'.e = J.e → ∀ t, J'.RF t = J.RF t) := by
  obtain ⟨k, J, hSA, hadm⟩ := exists_sa_adm hI hIm c hc
  refine ⟨J, hadm, fun J' hJ' => ⟨?_, fun he t => ?_⟩⟩
  · rw [← not_lt]
    rintro ⟨i, hbelow, hlt⟩
    simp only [Pi.toLex_apply] at hbelow hlt
    by_cases hik : (i : ℕ) < k
    · exact absurd (hSA.max J' hJ' i hik fun i' hi' => hbelow i' hi') (not_le.2 hlt)
    · rw [hSA.e_eq_zero (not_lt.1 hik)] at hlt
      exact absurd (J'.nonneg i) (not_le.2 hlt)
  · obtain ⟨c'', -, hRF, hx⟩ := hSA.dom J' hJ' (fun i _ => by rw [he])
    rw [← hRF, he, RF]
    exact Chart.RF_congr (fun i hi => hx i ((hSA.supp i).1 hi)) t

end MC

end BezoutCounterexample.Principalization
