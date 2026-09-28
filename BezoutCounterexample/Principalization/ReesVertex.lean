import BezoutCounterexample.Principalization.ReesGlobal

/-!
# The global Rees algebra: exceptional divisor, weak transform, vertex

Lemma 3.5 (1), (3), (5) (`lem:rees`) of the paper, and the vertex data for Theorem 3.6.

* `wcomp_mul`, `RF_mul_not_mem`, `compFil_mul_not_mem`: weighted initial forms multiply, so the
  associated graded ring is a domain; `span_s_isPrime`: the exceptional divisor `(s)` is prime.
* `isLocalization_away_s`: `R[1/s] = A[T^±]`; `weakT`, `map_eq_weakT`: `I R = s^d I_w`.
* `reesScale`: the `𝔾_m`-action `T ↦ μT`; `exists_reesScale_not_mem`: the polynomial argument.
* `comap_isMaximal_of_finiteType` (Zariski), `vertexG`, `isLocalization_VLoc`,
  `weakT_map_eq`, `homog_mem_reesRF`, `VertexData.vertexG_data`: the invariant of the weak
  transform at the global vertex.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization MvPowerSeries

section WComp

variable {n : ℕ} {K : Type*} [CommRing K] (w : Fin n → ℕ)

/-- The weight-`a` component of a power series. -/
def wcomp (a : ℕ) (F : MvPowerSeries (Fin n) K) : MvPowerSeries (Fin n) K :=
  fun β => if Finsupp.weight w β = a then coeff β F else 0

lemma coeff_wcomp (a : ℕ) (F : MvPowerSeries (Fin n) K) (β : Fin n →₀ ℕ) :
    coeff β (wcomp w a F) = if Finsupp.weight w β = a then coeff β F else 0 := rfl

/-- **Weighted initial forms multiply.** -/
lemma wcomp_mul {a b : ℕ} {F G : MvPowerSeries (Fin n) K}
    (hF : ∀ β, Finsupp.weight w β < a → coeff β F = 0)
    (hG : ∀ β, Finsupp.weight w β < b → coeff β G = 0) :
    wcomp w (a + b) (F * G) = wcomp w a F * wcomp w b G := by
  ext γ
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with hγ
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hwt : Finsupp.weight w p.1 + Finsupp.weight w p.2 = a + b := by
      rw [← map_add, hp, hγ]
    rw [coeff_wcomp, coeff_wcomp]
    by_cases h1 : Finsupp.weight w p.1 = a
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, zero_mul]
      rcases Nat.lt_or_gt_of_ne h1 with h | h
      · rw [hF _ h, zero_mul]
      · rw [hG _ (by omega), mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_wcomp, coeff_wcomp]
    split_ifs with h1 h2
    · exact absurd (by rw [← hp, map_add, h1, h2]) hγ
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]

end WComp

section LocalGr

lemma lam_eq_weight {n : ℕ} {e : Fin n → ℚ} {d : ℕ} (hd : 0 < d) {w : Fin n → ℕ}
    (hw : ∀ i, (w i : ℚ) = d * e i) (β : Fin n →₀ ℕ) : lam e β = (Finsupp.weight w β : ℚ) / d := by
  rw [Finsupp.weight_eq_sum, lam]
  push_cast
  rw [eq_div_iff (by exact_mod_cast hd.ne'), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, Nat.cast_mul, hw i]; ring

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}
  (c : Chart S n) (hc : c.IsCentred) {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {d : ℕ} (hd : 0 < d)
  {w : Fin n → ℕ} (hw : ∀ i, (w i : ℚ) = d * e i)
include hc he hd hw

lemma mem_RF_iff_weight (a : ℕ) (z : S) :
    z ∈ c.RF e ((a : ℚ) / d) ↔ ∀ β, Finsupp.weight w β < a → coeff β (c.tau z) = 0 := by
  rw [hc.mem_RF_iff he]
  refine forall_congr' fun β => imp_congr_left ?_
  rw [lam_eq_weight hd hw, div_lt_div_iff_of_pos_right (by exact_mod_cast hd)]
  exact Nat.cast_lt

/-- **The associated graded ring of a weighted filtration is a domain** (initial forms). -/
theorem RF_mul_not_mem [IsDomain (ResidueField S)] {a b : ℕ} {z z' : S}
    (hz : z ∈ c.RF e ((a : ℚ) / d)) (hz1 : z ∉ c.RF e (((a + 1 : ℕ) : ℚ) / d))
    (hz' : z' ∈ c.RF e ((b : ℚ) / d)) (hz'1 : z' ∉ c.RF e (((b + 1 : ℕ) : ℚ) / d)) :
    z * z' ∉ c.RF e (((a + b + 1 : ℕ) : ℚ) / d) := by
  rw [mem_RF_iff_weight c hc he hd hw] at hz hz' hz1 hz'1 ⊢
  push Not at hz1 hz'1 ⊢
  obtain ⟨β, hβ, hβne⟩ := hz1
  obtain ⟨β', hβ', hβ'ne⟩ := hz'1
  have hβa : Finsupp.weight w β = a := by
    by_contra h; exact hβne (hz β (by omega))
  have hβb : Finsupp.weight w β' = b := by
    by_contra h; exact hβ'ne (hz' β' (by omega))
  have hF : wcomp w a (c.tau z) ≠ 0 := fun h => hβne (by
    have := congrArg (coeff β) h
    rwa [coeff_wcomp, ite_eq_left hβa, map_zero] at this)
  have hG : wcomp w b (c.tau z') ≠ 0 := fun h => hβ'ne (by
    have := congrArg (coeff β') h
    rwa [coeff_wcomp, ite_eq_left hβb, map_zero] at this)
  have hmul := wcomp_mul w hz hz'
  rw [← map_mul] at hmul
  have hne : wcomp w (a + b) (c.tau (z * z')) ≠ 0 := by
    rw [hmul]; exact mul_ne_zero hF hG
  by_contra hall
  push Not at hall
  apply hne
  ext γ
  rw [coeff_wcomp, map_zero]
  split_ifs with hγ
  · exact hall γ (by omega)
  · rfl

end LocalGr

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

omit hd in
/-- The local data at a point of the component: a maximal centre with integral weights. -/
lemma exists_centre_data (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : 𝔭 ≤ 𝔪) :
    ∃ (n : ℕ) (J : MC (Localization.AtPrime 𝔪) n) (w : Fin n → ℕ),
      (∀ i, (w i : ℚ) = d * J.e i) ∧ ∀ t, cRF I 𝔪 t = J.RF t := by
  have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  obtain ⟨n, e, ⟨⟨J, hJ, hJe⟩, hmin⟩, hev⟩ := hZ.2
  have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
  have hw' : ∀ i : Fin n, ∃ w : ℕ, (w : ℚ) = d * J.e i := fun i => by
    obtain ⟨w, hw⟩ := hw i
    exact ⟨w, by rw [hw, ← hev, hJe, ext0_apply]⟩
  choose w hwe using hw'
  exact ⟨n, J, w, hwe, fun t => cRF_eq hI hZ.1 hJ hJi t⟩

omit hd hw in
lemma compFil_mem_iff (j : ℤ) (x : A) : x ∈ (compFil hI hmax h𝔭 d).F j ↔
    ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 →
      algebraMap A (Localization.AtPrime 𝔪) x ∈ cRF I 𝔪 ((j : ℚ) / d) := mem_compF

/-- **Torsion-freeness of the graded pieces**: a non-member of `F_{a+1}` is locally a
non-member at every point of the component. -/
theorem not_mem_loc {a : ℕ} {x : A} (hx : x ∈ (compFil hI hmax h𝔭 d).F a)
    (hx1 : x ∉ (compFil hI hmax h𝔭 d).F (a + 1)) (𝔪₀ : Ideal A) [𝔪₀.IsMaximal] (h𝔭𝔪₀ : 𝔭 ≤ 𝔪₀) :
    algebraMap A (Localization.AtPrime 𝔪₀) x ∉ cRF I 𝔪₀ (((a + 1 : ℕ) : ℚ) / d) := by
  intro hmem
  apply hx1
  -- a multiple `h x` with `h ∉ 𝔪₀` lies in `F_{a+1}`
  have h1 : algebraMap A (Localization.AtPrime 𝔪₀) x ∈
      ((compFil hI hmax h𝔭 d).F (a + 1)).map (algebraMap A _) := by
    rw [compFil_F, compF_map hI hmax h𝔭 𝔪₀ h𝔭𝔪₀]; push_cast at hmem ⊢; exact hmem
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪₀.primeCompl] at h1
  obtain ⟨h, hh, hhx⟩ := h1
  have hh𝔭 : h ∉ 𝔭 := fun h' => hh (h𝔭𝔪₀ h')
  rw [compFil_mem_iff]
  intro 𝔪 _ h𝔭𝔪
  obtain ⟨n, J, w, hwe, hcRF⟩ := exists_centre_data hI hmax h𝔭 hw 𝔪 h𝔭𝔪
  have hx' := (compFil_mem_iff hI hmax h𝔭 a x).1 hx 𝔪 h𝔭𝔪
  have hhx' := (compFil_mem_iff hI hmax h𝔭 (a + 1) (h * x)).1 hhx 𝔪 h𝔭𝔪
  rw [hcRF] at hx' hhx' ⊢
  by_contra hne
  -- `h` is not in `F_1 = 𝔭` locally
  have hh1 : algebraMap A (Localization.AtPrime 𝔪) h ∉ J.RF (((0 + 1 : ℕ) : ℚ) / d) := by
    intro hmem'
    rw [← hcRF] at hmem'
    have : algebraMap A (Localization.AtPrime 𝔪) h ∈
        (compF I 𝔭 (1 / d)).map (algebraMap A (Localization.AtPrime 𝔪)) := by
      rw [compF_map hI hmax h𝔭 𝔪 h𝔭𝔪]; simpa using hmem'
    rw [compF_one_div hI hmax h𝔭 hd hw] at this
    have hp := h𝔭.1.1
    rw [← under_map_atPrime h𝔭𝔪] at hh𝔭
    exact hh𝔭 this
  have hh0 : algebraMap A (Localization.AtPrime 𝔪) h ∈ J.RF (((0 : ℕ) : ℚ) / d) := by
    rw [Nat.cast_zero, zero_div, MC.RF, J.c.RF_of_nonpos J.nonneg le_rfl]; trivial
  have := RF_mul_not_mem J.c J.centred J.nonneg hd hwe hh0 hh1 hx'
    (by push_cast at hne ⊢; exact hne)
  rw [← map_mul] at this
  apply this
  push_cast at hhx' ⊢
  rw [zero_add]
  exact hhx'

/-- **The associated graded ring is a domain.** -/
theorem compFil_mul_not_mem {a b : ℕ} {x y : A} (hx : x ∈ (compFil hI hmax h𝔭 d).F a)
    (hx1 : x ∉ (compFil hI hmax h𝔭 d).F (a + 1)) (hy : y ∈ (compFil hI hmax h𝔭 d).F b)
    (hy1 : y ∉ (compFil hI hmax h𝔭 d).F (b + 1)) :
    x * y ∉ (compFil hI hmax h𝔭 d).F (a + b + 1) := by
  have := h𝔭.1.1
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹_›)
  have := h𝔪
  obtain ⟨n, J, w, hwe, hcRF⟩ := exists_centre_data hI hmax h𝔭 hw 𝔪 hle
  have hx' := (compFil_mem_iff hI hmax h𝔭 a x).1 hx 𝔪 hle
  have hy' := (compFil_mem_iff hI hmax h𝔭 b y).1 hy 𝔪 hle
  have hx1' := not_mem_loc hI hmax h𝔭 hd hw hx hx1 𝔪 hle
  have hy1' := not_mem_loc hI hmax h𝔭 hd hw hy hy1 𝔪 hle
  rw [hcRF] at hx' hy' hx1' hy1'
  intro hxy
  have hxy' := (compFil_mem_iff hI hmax h𝔭 (a + b + 1) (x * y)).1 hxy 𝔪 hle
  rw [hcRF, map_mul] at hxy'
  exact RF_mul_not_mem J.c J.centred J.nonneg hd hwe hx' hx1'
    hy' hy1' (by push_cast at hxy' ⊢; exact hxy')

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section Generic

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
include hneg

/-- The element `s = T⁻¹` of the extended Rees algebra. -/
def reesS : ReesAlg Φ :=
  ⟨T (-1), by
    have : (T (-1) : B[T;T⁻¹]) = LaurentPolynomial.C 1 * T (-1) := by simp
    rw [this]
    exact C_mul_T_mem_ReesAlg (by rw [hneg _ (by norm_num)]; trivial)⟩

omit [Algebra ℚ B] in
lemma reesS_coe : (reesS Φ hneg : B[T;T⁻¹]) = T (-1) := rfl

omit hneg [Algebra ℚ B] in
lemma mul_T_mem {p : B[T;T⁻¹]} (hp : ∀ j, p.coeff j ∈ Φ.F (j + 1)) : T 1 * p ∈ ReesAlg Φ := by
  intro j
  rw [coeff_T_mul]
  have := hp (j - 1)
  rwa [sub_add_cancel] at this

omit [Algebra ℚ B] in
/-- Membership in `(s)`. -/
theorem mem_span_s_iff (p : ReesAlg Φ) :
    p ∈ Ideal.span {reesS Φ hneg} ↔ ∀ j, (p : B[T;T⁻¹]).coeff j ∈ Φ.F (j + 1) := by
  constructor
  · intro h j
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 h
    show ((q : B[T;T⁻¹]) * T (-1)).coeff j ∈ _
    rw [mul_comm, coeff_T_mul, sub_neg_eq_add]
    exact q.2 (j + 1)
  · intro h
    refine Ideal.mem_span_singleton'.2 ⟨⟨T 1 * (p : B[T;T⁻¹]), mul_T_mem Φ h⟩, Subtype.ext ?_⟩
    show (T 1 * (p : B[T;T⁻¹]) * T (-1) : B[T;T⁻¹]) = (p : B[T;T⁻¹])
    rw [mul_comm, ← mul_assoc, ← T_add]; simp

omit [Algebra ℚ B] in
/-- **The exceptional divisor is prime** when the associated graded ring is a domain. -/
theorem span_s_isPrime (h1 : Φ.F 1 ≠ ⊤)
    (hgr : ∀ (a b : ℕ) (x y : B), x ∈ Φ.F a → x ∉ Φ.F (a + 1) → y ∈ Φ.F b → y ∉ Φ.F (b + 1) →
      x * y ∉ Φ.F ((a + b : ℕ) + 1)) :
    (Ideal.span {reesS Φ hneg}).IsPrime := by
  classical
  refine ⟨fun htop => ?_, fun {p q} hpq => ?_⟩
  · have h1mem : (1 : ReesAlg Φ) ∈ Ideal.span {reesS Φ hneg} := by rw [htop]; trivial
    have := (mem_span_s_iff Φ hneg 1).1 h1mem 0
    rw [show ((1 : ReesAlg Φ) : B[T;T⁻¹]) = 1 from rfl, coeff_one_laurent, ite_eq_left rfl] at this
    exact h1 ((Ideal.eq_top_iff_one _).2 (by simpa using this))
  by_contra hne
  push Not at hne
  obtain ⟨hp, hq⟩ := hne
  rw [mem_span_s_iff] at hp hq hpq
  push Not at hp hq
  -- minimal bad indices
  set Sp := (p : B[T;T⁻¹]).coeff.support.filter fun j => (p : B[T;T⁻¹]).coeff j ∉ Φ.F (j + 1)
  set Sq := (q : B[T;T⁻¹]).coeff.support.filter fun j => (q : B[T;T⁻¹]).coeff j ∉ Φ.F (j + 1)
  have hSp : Sp.Nonempty := by
    obtain ⟨j, hj⟩ := hp
    refine ⟨j, Finset.mem_filter.2 ⟨?_, hj⟩⟩
    rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hj; exact hj (zero_mem _)
  have hSq : Sq.Nonempty := by
    obtain ⟨j, hj⟩ := hq
    refine ⟨j, Finset.mem_filter.2 ⟨?_, hj⟩⟩
    rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hj; exact hj (zero_mem _)
  set j₀ := Sp.min' hSp
  set l₀ := Sq.min' hSq
  have hj₀ : (p : B[T;T⁻¹]).coeff j₀ ∉ Φ.F (j₀ + 1) := (Finset.mem_filter.1 (Sp.min'_mem hSp)).2
  have hl₀ : (q : B[T;T⁻¹]).coeff l₀ ∉ Φ.F (l₀ + 1) := (Finset.mem_filter.1 (Sq.min'_mem hSq)).2
  have hbelow_p : ∀ a < j₀, (p : B[T;T⁻¹]).coeff a ∈ Φ.F (a + 1) := by
    intro a ha
    by_contra h
    have hmem : a ∈ Sp := by
      refine Finset.mem_filter.2 ⟨?_, h⟩
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at h; exact h (zero_mem _)
    exact absurd (Sp.min'_le a hmem) (not_le.2 ha)
  have hbelow_q : ∀ b < l₀, (q : B[T;T⁻¹]).coeff b ∈ Φ.F (b + 1) := by
    intro b hb
    by_contra h
    have hmem : b ∈ Sq := by
      refine Finset.mem_filter.2 ⟨?_, h⟩
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at h; exact h (zero_mem _)
    exact absurd (Sq.min'_le b hmem) (not_le.2 hb)
  have hj₀nn : 0 ≤ j₀ := by
    by_contra h; push Not at h
    exact hj₀ (by rw [hneg _ (by omega)]; trivial)
  have hl₀nn : 0 ≤ l₀ := by
    by_contra h; push Not at h
    exact hl₀ (by rw [hneg _ (by omega)]; trivial)
  -- the coefficient of `pq` in degree `j₀ + l₀`
  have hcoeff := hpq (j₀ + l₀)
  have hexp : ((p * q : ReesAlg Φ) : B[T;T⁻¹]).coeff (j₀ + l₀) =
      ∑ a ∈ (p : B[T;T⁻¹]).coeff.support,
        (p : B[T;T⁻¹]).coeff a * (q : B[T;T⁻¹]).coeff (-a + (j₀ + l₀)) := by
    rw [show ((p * q : ReesAlg Φ) : B[T;T⁻¹]) = (p : B[T;T⁻¹]) * q from rfl,
      AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  have hj₀supp : j₀ ∈ (p : B[T;T⁻¹]).coeff.support := (Finset.mem_filter.1 (Sp.min'_mem hSp)).1
  rw [hexp, ← Finset.add_sum_erase _ _ hj₀supp] at hcoeff
  have hrest : ∑ a ∈ (p : B[T;T⁻¹]).coeff.support.erase j₀,
      (p : B[T;T⁻¹]).coeff a * (q : B[T;T⁻¹]).coeff (-a + (j₀ + l₀)) ∈ Φ.F (j₀ + l₀ + 1) := by
    refine Ideal.sum_mem _ fun a ha => ?_
    have ha' : a ≠ j₀ := Finset.ne_of_mem_erase ha
    rcases lt_or_gt_of_ne ha' with h | h
    · have h1 := hbelow_p a h
      have h2 := q.2 (-a + (j₀ + l₀))
      have := Φ.mul_le _ _ (Ideal.mul_mem_mul h1 h2)
      convert this using 2; ring
    · have h1 := p.2 a
      have h2 := hbelow_q (-a + (j₀ + l₀)) (by omega)
      have := Φ.mul_le _ _ (Ideal.mul_mem_mul h1 h2)
      convert this using 2; ring
  have hmain : (p : B[T;T⁻¹]).coeff j₀ * (q : B[T;T⁻¹]).coeff l₀ ∈ Φ.F (j₀ + l₀ + 1) := by
    have := Ideal.sub_mem _ hcoeff hrest
    rwa [add_sub_cancel_right, show -j₀ + (j₀ + l₀) = l₀ by ring] at this
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hj₀nn
  obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le hl₀nn
  have hpa := p.2 j₀
  have hqb := q.2 l₀
  rw [ha] at hpa hj₀ hmain
  rw [hb] at hqb hl₀ hmain
  exact hgr a b _ _ hpa hj₀ hqb hl₀ (by push_cast; exact hmain)

end Generic

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section Generic

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
include hneg

omit [Algebra ℚ B] in
lemma reesS_pow_coe (N : ℕ) : ((reesS Φ hneg ^ N : ReesAlg Φ) : B[T;T⁻¹]) = T (-(N : ℤ)) := by
  rw [SubmonoidClass.coe_pow, reesS_coe, T_pow]; congr 1; ring

omit [Algebra ℚ B] in
/-- **Inverting `s`** gives the Laurent polynomial ring. -/
theorem isLocalization_away_s : IsLocalization.Away (reesS Φ hneg) B[T;T⁻¹] := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, N, rfl⟩
    show IsUnit (((reesS Φ hneg ^ N : ReesAlg Φ) : B[T;T⁻¹]))
    rw [reesS_pow_coe]
    exact isUnit_T _
  · intro z
    classical
    set N : ℕ := (z.coeff.support.sup fun j => j.toNat)
    have hz : z * T (-(N : ℤ)) ∈ ReesAlg Φ := by
      intro j
      rw [mul_comm, coeff_T_mul]
      by_cases hj : j ≤ 0
      · rw [hneg j hj]; trivial
      · have : z.coeff (j - -(N : ℤ)) = 0 := by
          by_contra hne
          have hmem : j + N ∈ z.coeff.support := by
            rw [Finsupp.mem_support_iff]; simpa using hne
          have := Finset.le_sup (f := fun j : ℤ => j.toNat) hmem
          have h2 : (j + N).toNat ≤ N := this
          omega
        rw [this]; exact zero_mem _
    refine ⟨⟨⟨_, hz⟩, ⟨reesS Φ hneg ^ N, N, rfl⟩⟩, ?_⟩
    show z * ((reesS Φ hneg ^ N : ReesAlg Φ) : B[T;T⁻¹]) = z * T (-(N : ℤ))
    rw [reesS_pow_coe]
  · intro x y hxy
    exact ⟨1, by rw [Subtype.ext hxy]⟩

/-- The weak transform `(f T^d : f ∈ I)` of an ideal `I ⊆ F_d`. -/
def weakT (I : Ideal B) (d : ℤ) (hId : I ≤ Φ.F d) : Ideal (ReesAlg Φ) :=
  Ideal.span (Set.range fun f : I => (⟨LaurentPolynomial.C (f : B) * T d,
    C_mul_T_mem_ReesAlg (hId f.2)⟩ : ReesAlg Φ))

omit [Algebra ℚ B] in
/-- **`I R = s^d I_w`.** -/
theorem map_eq_weakT (I : Ideal B) (d : ℕ) (hId : I ≤ Φ.F d) :
    I.map (algebraMap B (ReesAlg Φ)) = Ideal.span {reesS Φ hneg ^ d} * weakT Φ I d hId := by
  rw [weakT, Ideal.span_mul_span, Ideal.map, Set.singleton_mul]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨_, ⟨⟨f, hf⟩, rfl⟩, Subtype.ext ?_⟩
    show ((reesS Φ hneg ^ d : ReesAlg Φ) : B[T;T⁻¹]) * (LaurentPolynomial.C f * T d) =
      algebraMap B B[T;T⁻¹] f
    rw [reesS_pow_coe, mul_left_comm, ← T_add, neg_add_cancel, T_zero, mul_one,
      LaurentPolynomial.C_eq_algebraMap]
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    refine ⟨f, f.2, Subtype.ext ?_⟩
    show algebraMap B B[T;T⁻¹] f = ((reesS Φ hneg ^ d : ReesAlg Φ) : B[T;T⁻¹]) *
      (LaurentPolynomial.C (f : B) * T d)
    rw [reesS_pow_coe, mul_left_comm, ← T_add, neg_add_cancel, T_zero, mul_one,
      LaurentPolynomial.C_eq_algebraMap]

end Generic

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- A semi-associated admissible centre computes the invariant. -/
lemma MC.SA.isInv {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S]
    {n : ℕ} {I : Ideal S} {k : ℕ} {J : MC S n} (hSA : MC.SA I k J) (hadm : J.Adm I) :
    IsInv I n J.e := by
  refine ⟨⟨J, hadm, rfl⟩, fun J' hJ' => ?_⟩
  rw [← not_lt]
  rintro ⟨i, hbelow, hlt⟩
  simp only [Pi.toLex_apply] at hbelow hlt
  by_cases hik : (i : ℕ) < k
  · exact absurd (hSA.max J' hJ' i hik fun i' hi' => hbelow i' hi') (not_le.2 hlt)
  · rw [hSA.e_eq_zero (not_lt.1 hik)] at hlt
    exact absurd (J'.nonneg i) (not_le.2 hlt)

section Vertex

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B]
  {n : ℕ} {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

include he hanti hd hw in
/-- **The invariant of the weak transform at the vertex.** -/
theorem vertex_isInv (c₀ : Chart B n) (hc₀ : c₀.IsCentred)
    (hF₀ : ∀ m, Φ.F m = chartFil c₀ e d m) {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)
    (hkn : k ≤ n) (I : Ideal B) (hI0 : I ≠ ⊥) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) :
    ∃ (c' : Chart B n) (hF' : ∀ m, Φ.F m = chartFil c' e d m),
      IsInv (S := VLoc hpos) (weakV hpos I hId) (n + 1) (pad (n + 1) e) ∧
      (vChart he hd hw hpos c' hF').IsCentred ∧
      weakV hpos I hId ≤ (vChart he hd hw hpos c' hF').RF (pad (n + 1) e) 1 := by
  have := VLoc_noeth hpos c₀ hF₀ he hd hw
  obtain ⟨c', hc', hF', hSA⟩ := vertex_invariant he hanti hd hw hpos c₀ hc₀ hF₀ hsupp hkn I hI0 hId hmax
  have hadm : weakV hpos I hId ≤ (vChart he hd hw hpos c' hF').RF (pad (n + 1) e) 1 := by
    rw [vChart, Chart.localization_RF]
    exact Ideal.map_mono (weak_le_reesRF he hd hw c' hF' I hId)
  exact ⟨c', hF', hSA.isInv hadm, vChart_isCentred he hd hw hpos c' hF' hc', hadm⟩

end Vertex

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section Scale

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- The unit `μ T` of the Laurent polynomial ring. -/
def scaleUnit (μ : Bˣ) : (B[T;T⁻¹])ˣ :=
  ⟨LaurentPolynomial.C (μ : B) * T 1, LaurentPolynomial.C (↑μ⁻¹ : B) * T (-1), by
    rw [mul_mul_mul_comm, ← map_mul, ← T_add, Units.mul_inv]; simp, by
    rw [mul_mul_mul_comm, ← map_mul, ← T_add, Units.inv_mul]; simp⟩

/-- The rescaling `T ↦ μ T`. -/
def lscale (μ : Bˣ) : B[T;T⁻¹] →+* B[T;T⁻¹] := LaurentPolynomial.eval₂ LaurentPolynomial.C (scaleUnit μ)

omit [Algebra ℚ B] in
lemma scaleUnit_pow (μ : Bˣ) (n : ℕ) :
    ((scaleUnit μ ^ n : (B[T;T⁻¹])ˣ) : B[T;T⁻¹]) = LaurentPolynomial.C (↑(μ ^ n) : B) * T n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, pow_succ, Units.val_mul, map_mul]
    simp only [scaleUnit, Units.val_mk]
    rw [show ((n + 1 : ℕ) : ℤ) = n + 1 by push_cast; ring, T_add]
    ring

omit [Algebra ℚ B] in
lemma scaleUnit_zpow (μ : Bˣ) (j : ℤ) :
    ((scaleUnit μ ^ j : (B[T;T⁻¹])ˣ) : B[T;T⁻¹]) = LaurentPolynomial.C (↑(μ ^ j) : B) * T j := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [zpow_natCast, zpow_natCast, scaleUnit_pow]
  · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    have h1 := scaleUnit_pow μ n
    -- the inverse of `C (μ^n) * T n`
    have hXY : ((scaleUnit μ ^ n : (B[T;T⁻¹])ˣ) : B[T;T⁻¹]) *
        (LaurentPolynomial.C (↑(μ ^ n)⁻¹ : B) * T (-(n : ℤ))) = 1 := by
      rw [h1, mul_mul_mul_comm, ← map_mul, ← T_add, Units.mul_inv]; simp
    have hinv : (((scaleUnit μ ^ n)⁻¹ : (B[T;T⁻¹])ˣ) : B[T;T⁻¹]) =
        LaurentPolynomial.C (↑(μ ^ n)⁻¹ : B) * T (-(n : ℤ)) := by
      calc (((scaleUnit μ ^ n)⁻¹ : (B[T;T⁻¹])ˣ) : B[T;T⁻¹])
          = (((scaleUnit μ ^ n)⁻¹ : (B[T;T⁻¹])ˣ) : B[T;T⁻¹]) * (((scaleUnit μ ^ n : (B[T;T⁻¹])ˣ) : B[T;T⁻¹]) *
            (LaurentPolynomial.C (↑(μ ^ n)⁻¹ : B) * T (-(n : ℤ)))) := by rw [hXY, mul_one]
        _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
    exact hinv

omit [Algebra ℚ B] in
lemma lscale_C_mul_T (μ : Bˣ) (b : B) (j : ℤ) :
    lscale μ (LaurentPolynomial.C b * T j) = LaurentPolynomial.C (b * ↑(μ ^ j)) * T j := by
  rw [lscale, eval₂_C_mul_T, scaleUnit_zpow, map_mul, mul_assoc]

end Scale

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section Scale

variable {B : Type*} [CommRing B] [Algebra ℚ B]

omit [Algebra ℚ B] in
lemma lscale_coeff (μ : Bˣ) (p : B[T;T⁻¹]) (j : ℤ) :
    (lscale μ p).coeff j = p.coeff j * ↑(μ ^ j) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, add_mul]
  | C_mul_T l b =>
    rw [lscale_C_mul_T, coeff_C_mul_T, coeff_C_mul_T]
    split_ifs with h
    · subst h; rfl
    · rw [zero_mul]

omit [Algebra ℚ B] in
lemma lscale_lscale (μ ν : Bˣ) (p : B[T;T⁻¹]) : lscale μ (lscale ν p) = lscale (μ * ν) p := by
  ext j
  rw [lscale_coeff, lscale_coeff, lscale_coeff, mul_assoc, ← Units.val_mul, ← mul_zpow, mul_comm ν]

omit [Algebra ℚ B] in
lemma lscale_one (p : B[T;T⁻¹]) : lscale 1 p = p := by
  ext j; rw [lscale_coeff, one_zpow, Units.val_one, mul_one]

variable (Φ : WFil B)

omit [Algebra ℚ B] in
lemma lscale_mem {μ : Bˣ} {p : B[T;T⁻¹]} (hp : p ∈ ReesAlg Φ) : lscale μ p ∈ ReesAlg Φ := by
  intro j
  rw [lscale_coeff]
  exact Ideal.mul_mem_right _ _ (hp j)

/-- The rescaling automorphism `ρ_μ : T ↦ μ T` of the extended Rees algebra. -/
def reesScale (μ : Bˣ) : ReesAlg Φ ≃+* ReesAlg Φ where
  toFun p := ⟨lscale μ p, lscale_mem Φ p.2⟩
  invFun p := ⟨lscale μ⁻¹ p, lscale_mem Φ p.2⟩
  left_inv p := Subtype.ext (by
    show lscale μ⁻¹ (lscale μ p) = p
    rw [lscale_lscale, inv_mul_cancel, lscale_one])
  right_inv p := Subtype.ext (by
    show lscale μ (lscale μ⁻¹ p) = p
    rw [lscale_lscale, mul_inv_cancel, lscale_one])
  map_mul' p q := Subtype.ext (by simp)
  map_add' p q := Subtype.ext (by simp)

omit [Algebra ℚ B] in
lemma reesScale_coe (μ : Bˣ) (p : ReesAlg Φ) :
    ((reesScale Φ μ p : ReesAlg Φ) : B[T;T⁻¹]) = lscale μ p := rfl

end Scale

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section Poly

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)

/-- A nonzero rational as a unit of a `ℚ`-algebra. -/
def qUnit (μ : ℚ) (hμ : μ ≠ 0) : Bˣ := ((isUnit_iff_ne_zero.2 hμ).map (algebraMap ℚ B)).unit

lemma qUnit_val (μ : ℚ) (hμ : μ ≠ 0) : ((qUnit μ hμ : Bˣ) : B) = algebraMap ℚ B μ := rfl

/-- The homogeneous components of an element of the Rees algebra. -/
def hcomp (p : ReesAlg Φ) (j : ℤ) : ReesAlg Φ :=
  ⟨LaurentPolynomial.C ((p : B[T;T⁻¹]).coeff j) * T j, C_mul_T_mem_ReesAlg (p.2 j)⟩

omit [Algebra ℚ B] in
lemma sum_hcomp (p : ReesAlg Φ) : ∑ j ∈ (p : B[T;T⁻¹]).coeff.support, hcomp Φ p j = p := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single (p : B[T;T⁻¹])]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [single_eq_C_mul_T]; rfl

omit [Algebra ℚ B] in
lemma reesScale_hcomp (μ : Bˣ) (p : ReesAlg Φ) (j : ℤ) :
    reesScale Φ μ (hcomp Φ p j) = algebraMap B (ReesAlg Φ) ↑(μ ^ j) * hcomp Φ p j := by
  apply Subtype.ext
  rw [reesScale_coe]
  show lscale μ (LaurentPolynomial.C ((p : B[T;T⁻¹]).coeff j) * T j) =
    algebraMap B B[T;T⁻¹] ↑(μ ^ j) * (LaurentPolynomial.C ((p : B[T;T⁻¹]).coeff j) * T j)
  rw [lscale_C_mul_T, ← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul, mul_comm (↑(μ ^ j) : B)]

include hneg

omit [Algebra ℚ B] in
lemma hcomp_neg_mem (P : Ideal (ReesAlg Φ)) (hs : reesS Φ hneg ∈ P) (p : ReesAlg Φ) {j : ℤ}
    (hj : j < 0) : hcomp Φ p j ∈ P := by
  have : hcomp Φ p j = algebraMap B (ReesAlg Φ) ((p : B[T;T⁻¹]).coeff j) *
      reesS Φ hneg ^ (-j).toNat := by
    apply Subtype.ext
    show (LaurentPolynomial.C ((p : B[T;T⁻¹]).coeff j) * T j : B[T;T⁻¹]) =
      algebraMap B B[T;T⁻¹] ((p : B[T;T⁻¹]).coeff j) *
        ((reesS Φ hneg ^ (-j).toNat : ReesAlg Φ) : B[T;T⁻¹])
    rw [reesS_pow_coe, ← LaurentPolynomial.C_eq_algebraMap]
    congr 2; omega
  rw [this]
  exact P.mul_mem_left _ (P.pow_mem_of_mem hs _ (by omega))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The polynomial argument**: some rescaling moves `G` off a maximal ideal containing `s`, if
its degree-zero part is not in it. -/
theorem exists_reesScale_not_mem (P : Ideal (ReesAlg Φ)) [hP : P.IsMaximal]
    (hs : reesS Φ hneg ∈ P) (G : ReesAlg Φ) (hG : hcomp Φ G 0 ∉ P) :
    ∃ (μ : ℚ) (hμ : μ ≠ 0), reesScale Φ (qUnit μ hμ) G ∉ P := by
  classical
  have : P.IsPrime := hP.isPrime
  let : CommRing (ReesAlg Φ ⧸ P) := Ideal.Quotient.commRing P
  let π : ReesAlg Φ →+* ReesAlg Φ ⧸ P := Ideal.Quotient.mk P
  set S := (G : B[T;T⁻¹]).coeff.support
  set Q : Polynomial (ReesAlg Φ ⧸ P) := ∑ j ∈ S.filter (fun j => 0 ≤ j),
    (Polynomial.C (π (hcomp Φ G j)) * (Polynomial.X : Polynomial (ReesAlg Φ ⧸ P)) ^ j.toNat)
  have hQ0 : Q.coeff 0 = π (hcomp Φ G 0) := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    by_cases h0 : (0 : ℤ) ∈ S
    · rw [Finset.sum_eq_single (0 : ℤ)]
      · simp
      · intro j hj hj0
        rw [ite_eq_right]; rw [Finset.mem_filter] at hj; omega
      · intro h; exact absurd (Finset.mem_filter.2 ⟨h0, le_rfl⟩) h
    · have hG0 : hcomp Φ G 0 = 0 := by
        apply Subtype.ext
        show LaurentPolynomial.C ((G : B[T;T⁻¹]).coeff 0) * T 0 = 0
        rw [Finsupp.notMem_support_iff.1 h0, map_zero, zero_mul]
      rw [hG0, map_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      rw [ite_eq_right]; intro h; apply h0; have : j = 0 := by omega
      rw [← this]; exact hj.1
  have hQne : Q ≠ 0 := by
    intro h
    apply hG
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hQ0, h, Polynomial.coeff_zero]
  -- evaluation of `Q` at `μ`
  have heval : ∀ (μ : ℚ) (hμ : μ ≠ 0),
      π (reesScale Φ (qUnit μ hμ) G) = Q.eval (algebraMap ℚ (ReesAlg Φ ⧸ P) μ) := by
    intro μ hμ
    conv_lhs => rw [← sum_hcomp Φ G]
    rw [map_sum, map_sum]
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun j => 0 ≤ j)]
    have hneg0 : ∑ j ∈ S.filter (fun j => ¬ 0 ≤ j), π (reesScale Φ (qUnit μ hμ) (hcomp Φ G j)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      rw [reesScale_hcomp, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (hcomp_neg_mem Φ hneg P hs G (by omega)), mul_zero]
    rw [hneg0, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_filter] at hj
    rw [reesScale_hcomp, map_mul, mul_comm]
    congr 1
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hj.2
    subst hm
    rw [zpow_natCast, Units.val_pow_eq_pow_val, qUnit_val, map_pow, map_pow, Int.toNat_natCast]
    rfl
  -- choose `μ` avoiding the roots
  obtain ⟨μ, hμ⟩ := Infinite.exists_notMem_finset
    (insert (0 : ℚ) ((Q.roots.toFinset).preimage (algebraMap ℚ (ReesAlg Φ ⧸ P))
      ((algebraMap ℚ (ReesAlg Φ ⧸ P)).injective.injOn)))
  rw [Finset.mem_insert, not_or, Finset.mem_preimage, Multiset.mem_toFinset] at hμ
  obtain ⟨hμ0, hμr⟩ := hμ
  refine ⟨μ, hμ0, fun hmem => hμr ?_⟩
  rw [Polynomial.mem_roots hQne, Polynomial.IsRoot, ← heval μ hμ0]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hmem

end Poly

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- The contraction of a maximal ideal along a map of finitely generated `ℚ`-algebras is maximal
(Zariski's lemma). -/
lemma comap_isMaximal_of_finiteType {A R : Type*} [CommRing A] [CommRing R] [Algebra ℚ A]
    [Algebra ℚ R] [Algebra A R] [IsScalarTower ℚ A R] [Algebra.FiniteType ℚ R] (P : Ideal R)
    [hP : P.IsMaximal] : (P.comap (algebraMap A R)).IsMaximal := by
  set 𝔪 := P.comap (algebraMap A R)
  have : 𝔪.IsPrime := Ideal.comap_isPrime _ _
  let := Ideal.Quotient.field P
  have : Module.Finite ℚ (R ⧸ P) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ P)
  let φ : (A ⧸ 𝔪) →ₐ[ℚ] (R ⧸ P) :=
    Ideal.quotientMapₐ P (IsScalarTower.toAlgHom ℚ A R) le_rfl
  have hφ : Function.Injective φ := Ideal.quotientMap_injective
  have : Module.Finite ℚ (A ⧸ 𝔪) := Module.Finite.of_injective φ.toLinearMap hφ
  have : IsArtinianRing (A ⧸ 𝔪) := IsArtinianRing.of_finite ℚ (A ⧸ 𝔪)
  exact Ideal.Quotient.maximal_of_isField 𝔪 (IsArtinianRing.isField_of_isDomain _)

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section LocalVertex

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsDomain B] (Φ : WFil B)
  (𝔪 : Ideal B) [𝔪.IsMaximal]
  (hpos : ∀ j : ℤ, 0 < j → (Φ.loc (Localization.AtPrime 𝔪)).F j ≤
    maximalIdeal (Localization.AtPrime 𝔪))

/-- The vertex over `𝔪`, as an ideal of the global Rees algebra. -/
def vertexG : Ideal (ReesAlg Φ) := (vertex hpos).comap (reesMap Φ (Localization.AtPrime 𝔪))

omit [IsDomain B] [Algebra ℚ B] in
lemma mem_vertexG (p : ReesAlg Φ) : p ∈ vertexG Φ 𝔪 hpos ↔ (p : B[T;T⁻¹]).coeff 0 ∈ 𝔪 := by
  rw [vertexG, Ideal.mem_comap, mem_vertex, reesMap_coe, lmap_coeff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪]

instance vertexG_isMaximal : (vertexG Φ 𝔪 hpos).IsMaximal := by
  have hsurj : Function.Surjective ((vtx hpos).comp (reesMap Φ (Localization.AtPrime 𝔪))) := by
    intro z
    obtain ⟨q, hq⟩ := (Ideal.bijective_algebraMap_quotient_residueField 𝔪).2 z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨algebraMap B (ReesAlg Φ) a, ?_⟩
    rw [← hq]
    show residue _ ((lmap (algebraMap B (Localization.AtPrime 𝔪)) (algebraMap B B[T;T⁻¹] a)).coeff 0) =
      algebraMap (B ⧸ 𝔪) 𝔪.ResidueField (Ideal.Quotient.mk 𝔪 a)
    rw [lmap_coeff, ← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.C_apply, ite_eq_left rfl]
    rfl
  have : vertexG Φ 𝔪 hpos = RingHom.ker ((vtx hpos).comp (reesMap Φ (Localization.AtPrime 𝔪))) := by
    ext p; rw [vertexG, Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]; rfl
  rw [this]
  exact RingHom.ker_isMaximal_of_surjective _ hsurj

end LocalVertex

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section LocalVertex2

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsDomain B] (Φ : WFil B)
  (𝔪 : Ideal B) [𝔪.IsMaximal]
  (hpos : ∀ j : ℤ, 0 < j → (Φ.loc (Localization.AtPrime 𝔪)).F j ≤
    maximalIdeal (Localization.AtPrime 𝔪))

/-- The algebra structure `R → R_𝔪`. -/
abbrev reesAlgLoc : Algebra (ReesAlg Φ) (ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) :=
  (reesMap Φ (Localization.AtPrime 𝔪)).toAlgebra

omit [Algebra ℚ B] in
/-- **The vertex local ring is the localization of the global Rees algebra at the global
vertex.** -/
theorem isLocalization_VLoc :
    letI := reesAlgLoc Φ 𝔪
    IsLocalization.AtPrime (VLoc hpos) (vertexG Φ 𝔪 hpos) := by
  let := reesAlgLoc Φ 𝔪
  have : IsLocalization (𝔪.primeCompl.map (algebraMap B (ReesAlg Φ)))
      (ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) :=
    reesMap_isLocalization Φ (Localization.AtPrime 𝔪) 𝔪.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors 𝔪)
  exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (𝔪.primeCompl.map (algebraMap B (ReesAlg Φ))) (VLoc hpos) (vertex hpos)

end LocalVertex2

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section WeakLoc

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsDomain B] (Φ : WFil B)
  (𝔪 : Ideal B) [𝔪.IsMaximal]

omit [Algebra ℚ B] [IsDomain B] in
lemma weak_map_le (I : Ideal B) (d : ℕ) (hId : I ≤ Φ.F d) :
    I.map (algebraMap B (Localization.AtPrime 𝔪)) ≤ (Φ.loc (Localization.AtPrime 𝔪)).F d :=
  Ideal.map_mono hId

omit [IsDomain B] in
/-- **The weak transform localizes.** -/
theorem weakT_map_eq (I : Ideal B) (d : ℕ) (hId : I ≤ Φ.F d) :
    (weakT Φ I d hId).map (reesMap Φ (Localization.AtPrime 𝔪)) =
      weakIdeal (d := d) (Φ := Φ.loc (Localization.AtPrime 𝔪))
        (I.map (algebraMap B (Localization.AtPrime 𝔪))) (weak_map_le Φ 𝔪 I d hId) := by
  apply le_antisymm
  · rw [weakT, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    apply Ideal.subset_span
    refine ⟨⟨algebraMap B _ f, Ideal.mem_map_of_mem _ f.2⟩, Subtype.ext ?_⟩
    show LaurentPolynomial.C (algebraMap B (Localization.AtPrime 𝔪) f) * T d =
      lmap (algebraMap B (Localization.AtPrime 𝔪)) (LaurentPolynomial.C (f : B) * T d)
    rw [lmap_C_mul_T]
  · rw [weakIdeal, Ideal.span_le]
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨⟨f, s⟩, hfs⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔪.primeCompl
      (Localization.AtPrime 𝔪)).1 hg
    simp only at hfs
    -- `g Tᵈ = s⁻¹ · (f Tᵈ)`
    set u : ReesAlg (Φ.loc (Localization.AtPrime 𝔪)) :=
      algebraMap (Localization.AtPrime 𝔪) _ (IsLocalization.mk' _ (1 : B) s)
    have hkey : (⟨LaurentPolynomial.C g * T d, C_mul_T_mem_ReesAlg (weak_map_le Φ 𝔪 I d hId hg)⟩ :
        ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) =
        u * reesMap Φ (Localization.AtPrime 𝔪)
          ⟨LaurentPolynomial.C (f : B) * T d, C_mul_T_mem_ReesAlg (hId f.2)⟩ := by
      apply Subtype.ext
      show LaurentPolynomial.C g * T d = algebraMap (Localization.AtPrime 𝔪) _
          (IsLocalization.mk' _ (1 : B) s) *
        lmap (algebraMap B (Localization.AtPrime 𝔪)) (LaurentPolynomial.C (f : B) * T d)
      rw [lmap_C_mul_T, ← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul, ← hfs,
        mul_comm g, ← mul_assoc, IsLocalization.mk'_spec, map_one, one_mul]
    show (⟨LaurentPolynomial.C g * T d, C_mul_T_mem_ReesAlg (weak_map_le Φ 𝔪 I d hId hg)⟩ :
        ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) ∈ _
    rw [hkey]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨f, rfl⟩))

end WeakLoc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section HomogRF

variable {B : Type*} [CommRing B] [Algebra ℚ B] {n : ℕ}
variable (c : Chart B n) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil B} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i)
include hF he hd hw

/-- **Homogeneous elements of positive degree lie in the Rees centre.** -/
theorem homog_mem_reesRF {j : ℤ} (hj : 1 ≤ j) {g : B} (hg : g ∈ Φ.F j) :
    (⟨LaurentPolynomial.C g * T j, C_mul_T_mem_ReesAlg hg⟩ : ReesAlg Φ) ∈
      (reesChart c hF he hd hw).RF (pad (n + 1) e) (1 / d) := by
  classical
  set Rc := (reesChart c hF he hd hw).RF (pad (n + 1) e) (1 / d)
  have hg' : g ∈ c.RF e ((j : ℚ) / d) := by rw [← chartFil, ← hF]; exact hg
  have hmem : ∀ g' (hg' : g' ∈ c.RF e ((j : ℚ) / d)),
      (⟨LaurentPolynomial.C g' * T j, C_mul_T_mem_ReesAlg (by rw [hF]; exact hg')⟩ :
        ReesAlg Φ) ∈ Rc := by
    intro g' hg'
    induction hg' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, h0, hα, rfl⟩ := hx
      have hwt := weight_ge_of_mem hd hw hα
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (Finsupp.weight w α : ℤ) - j = m :=
        ⟨((Finsupp.weight w α : ℤ) - j).toNat, by omega⟩
      rw [rees_mono_eq c hF he hd hw α j m hm]
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ?_)
      refine ⟨Finsupp.mapDomain Fin.castSucc α, fun i hi => ?_, ?_, ?_⟩
      · cases i using Fin.lastCases with
        | last => exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
        | cast i =>
          rw [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n)]
          apply h0
          simpa [pad] using hi
      · have : lam (pad (n + 1) e) (Finsupp.mapDomain Fin.castSucc α) = lam e α :=
          lam_pad (Nat.le_succ n) e α
        rw [this]
        refine le_trans ?_ hα
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast hd)]
        exact_mod_cast hj
      · rw [Fin.prod_univ_castSucc]
        simp only [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n), reesChart_x]
        rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), pow_zero, mul_one]
    | zero =>
      have : (⟨LaurentPolynomial.C 0 * T j, C_mul_T_mem_ReesAlg (by rw [hF]; exact zero_mem _)⟩ :
          ReesAlg Φ) = 0 := Subtype.ext (by simp)
      rw [this]; exact zero_mem _
    | add x y hx hy ihx ihy =>
      have : (⟨LaurentPolynomial.C (x + y) * T j, C_mul_T_mem_ReesAlg (by rw [hF]; exact add_mem hx hy)⟩ :
          ReesAlg Φ) = ⟨LaurentPolynomial.C x * T j, C_mul_T_mem_ReesAlg (by rw [hF]; exact hx)⟩ +
            ⟨LaurentPolynomial.C y * T j, C_mul_T_mem_ReesAlg (by rw [hF]; exact hy)⟩ :=
        Subtype.ext (by simp [add_mul])
      rw [this]; exact add_mem ihx ihy
    | smul b x hx ihx =>
      have : (⟨LaurentPolynomial.C (b • x) * T j,
          C_mul_T_mem_ReesAlg (by rw [hF]; exact Submodule.smul_mem _ b hx)⟩ : ReesAlg Φ) =
          algebraMap B (ReesAlg Φ) b * ⟨LaurentPolynomial.C x * T j,
            C_mul_T_mem_ReesAlg (by rw [hF]; exact hx)⟩ := by
        apply Subtype.ext
        show LaurentPolynomial.C (b • x) * T j = algebraMap B B[T;T⁻¹] b * (LaurentPolynomial.C x * T j)
        rw [smul_eq_mul, map_mul, ← LaurentPolynomial.C_eq_algebraMap, mul_assoc]
      rw [this]; exact Ideal.mul_mem_left _ _ ihx
  exact hmem g hg'

end HomogRF

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭

/-- The ideal lies in the `d`-th step of the filtration. -/
lemma I_le_compFil (hd : 0 < d) : I ≤ (compFil hI hmax h𝔭 d).F d := by
  intro f hf
  rw [compFil_F, mem_compF]
  intro 𝔪 _ h𝔭𝔪
  have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  obtain ⟨n, e, ⟨⟨J, hJ, hJe⟩, hmin⟩, -⟩ := hZ.2
  have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
  rw [cRF_eq hI hZ.1 hJ hJi, show ((d : ℤ) : ℚ) / d = 1 by
    push_cast; exact div_self (by exact_mod_cast hd.ne')]
  exact hJ (Ideal.mem_map_of_mem _ hf)

/-- The local chart data at a point of the component, packaged for the vertex. -/
structure VertexData (𝔪 : Ideal A) [𝔪.IsMaximal] where
  n : ℕ
  J : MC (Localization.AtPrime 𝔪) n
  w : Fin n → ℕ
  k : ℕ
  hwe : ∀ i, (w i : ℚ) = d * J.e i
  hadm : J.Adm (Iloc I 𝔪)
  hinv : IsInv (Iloc I 𝔪) n J.e
  hev : ext0 J.e = v₀
  hsupp : ∀ i, J.e i ≠ 0 ↔ (i : ℕ) < k
  hkn : k ≤ n
  hF : ∀ m, ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)).F m = chartFil J.c J.e d m

include hw in
lemma VertexData.nonempty (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : 𝔭 ≤ 𝔪) :
    Nonempty (VertexData hI hmax h𝔭 (d := d) (v₀ := v₀) 𝔪) := by
  have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  obtain ⟨n, e, ⟨⟨J, hJ, hJe⟩, hmin⟩, hev⟩ := hZ.2
  have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
  have := residueField_isIntegral 𝔪
  obtain ⟨k, ck, hrun, -, -, hsupp⟩ := hJi.exists_run (Iloc_ne_bot hI 𝔪) (Iloc_le hZ.1) J.c
    J.centred
  have hw' : ∀ i : Fin n, ∃ w : ℕ, (w : ℚ) = d * J.e i := fun i => by
    obtain ⟨w, hw⟩ := hw i
    exact ⟨w, by rw [hw, ← hev, hJe, ext0_apply]⟩
  choose w hwe using hw'
  exact ⟨⟨n, J, w, k, hwe, hJ, hJi, by rw [hJe, hev], hsupp, hrun.stage_le (Nat.zero_le _),
    fun m => by rw [compFil_loc_F hI hmax h𝔭 d 𝔪 h𝔭𝔪, cRF_eq hI hZ.1 hJ hJi]; rfl⟩⟩

variable {hI hmax h𝔭}

lemma VertexData.hpos {𝔪 : Ideal A} [𝔪.IsMaximal] (D : VertexData hI hmax h𝔭 (d := d) (v₀ := v₀) 𝔪)
    (hd : 0 < d) : ∀ j : ℤ, 0 < j → ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)).F j ≤
      maximalIdeal (Localization.AtPrime 𝔪) := fun j hj => by
  rw [D.hF]
  exact D.J.centred.RF_le_maximalIdeal (div_pos (by exact_mod_cast hj) (by exact_mod_cast hd))

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

section RingEquivTransport

variable {S S' : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [CommRing S'] [Algebra ℚ S']
  [IsLocalRing S'] {n : ℕ}

/-- A ring isomorphism of `ℚ`-algebras as a `ℚ`-algebra isomorphism. -/
def ringEquivQ (φ : S ≃+* S') : S ≃ₐ[ℚ] S' :=
  AlgEquiv.ofRingEquiv (f := φ) (fun q => RingHom.map_rat_algebraMap φ.toRingHom q)

omit [IsLocalRing S] [IsLocalRing S'] in
lemma map_ringEquivQ (φ : S ≃+* S') (I : Ideal S) : I.map (ringEquivQ φ) = I.map φ := by
  apply le_antisymm <;> rw [Ideal.map_le_iff_le_comap] <;> intro x hx <;>
    exact Ideal.mem_map_of_mem _ hx

lemma IsInv.mapRingEquiv {I : Ideal S} {e : Fin n → ℚ} (h : IsInv I n e) (φ : S ≃+* S') :
    IsInv (I.map φ) n e := by
  have := h.mapEquiv (ringEquivQ φ)
  rwa [map_ringEquivQ] at this

/-- Transport of a marked centre along a ring isomorphism. -/
def MC.mapRingEquiv (φ : S ≃+* S') (J : MC S n) : MC S' n := J.mapEquiv (ringEquivQ φ)

lemma MC.mapRingEquiv_RF (φ : S ≃+* S') (J : MC S n) (t : ℚ) :
    (J.mapRingEquiv φ).RF t = (J.RF t).map φ := by
  show (J.c.mapEquiv (ringEquivQ φ)).RF J.e t = _
  rw [Chart.mapEquiv_RF, map_ringEquivQ]; rfl

lemma MC.Adm.mapRingEquiv {I : Ideal S} {J : MC S n} (h : J.Adm I) (φ : S ≃+* S') :
    (J.mapRingEquiv φ).Adm (I.map φ) := by
  have := h.mapEquiv (ringEquivQ φ)
  rwa [map_ringEquivQ] at this

end RingEquivTransport

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} {hI : I ≠ ⊥} {v₀ : ℕ → ℚ}
  {hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v}
  {𝔭 : Ideal A} {h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes} {d : ℕ} (hd : 0 < d)

set_option maxHeartbeats 800000 in
/-- **The weak transform at the global vertex.** -/
theorem VertexData.vertexG_data {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : VertexData hI hmax h𝔭 (d := d) (v₀ := v₀) 𝔪) :
    ∃ J₀ : MC (Localization.AtPrime (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd))) (D.n + 1),
      J₀.Adm (Iloc (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd))
        (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd))) ∧
      J₀.e = pad (D.n + 1) D.J.e ∧
      IsInv (Iloc (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd))
        (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd))) (D.n + 1) J₀.e ∧
      ∀ (j : ℤ), 1 ≤ j → ∀ (f : A) (hf : f ∈ (compFil hI hmax h𝔭 d).F j),
        algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
          (Localization.AtPrime (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd)))
          ⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ ∈ J₀.RF (1 / d) := by
  set Φ := compFil hI hmax h𝔭 d
  set R := ReesAlg Φ
  set hpos := D.hpos hd
  set P₀ := vertexG Φ 𝔪 hpos
  set hId := I_le_compFil hI hmax h𝔭 hd
  have hIdm : Iloc I 𝔪 ≤ (Φ.loc (Localization.AtPrime 𝔪)).F d := Ideal.map_mono hId
  have : IsNoetherianRing (Localization.AtPrime 𝔪) := inferInstance
  obtain ⟨c', hF', hinvV, hcentV, hadmV⟩ := vertex_isInv D.J.nonneg D.J.anti hd D.hwe hpos D.J.c
    D.J.centred D.hF D.hsupp D.hkn (Iloc I 𝔪) (Iloc_ne_bot hI 𝔪) hIdm D.hinv.2
  let := reesAlgLoc Φ 𝔪
  have : IsLocalization.AtPrime (VLoc hpos) P₀ := isLocalization_VLoc Φ 𝔪 hpos
  let eV : Localization.AtPrime P₀ ≃ₐ[R] VLoc hpos :=
    IsLocalization.algEquiv P₀.primeCompl (Localization.AtPrime P₀) (VLoc hpos)
  let eq : VLoc hpos ≃+* Localization.AtPrime P₀ := eV.symm.toRingEquiv
  have heq : ∀ x : R, eq (algebraMap R (VLoc hpos) x) = algebraMap R (Localization.AtPrime P₀) x :=
    fun x => eV.symm.commutes x
  have hVR : ∀ x : R, algebraMap (ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) (VLoc hpos)
      (reesMap Φ (Localization.AtPrime 𝔪) x) = algebraMap R (VLoc hpos) x := fun x => rfl
  -- the weak transforms correspond
  have hweak : (weakV hpos (Iloc I 𝔪) hIdm).map eq =
      Iloc (weakT Φ I d hId) P₀ := by
    show (weakV hpos (Iloc I 𝔪) hIdm).map (eq : VLoc hpos →+* Localization.AtPrime P₀) = _
    rw [weakV, ← weakT_map_eq Φ 𝔪 I d hId, Ideal.map_map, Ideal.map_map]
    congr 1
    ext x
    simp only [RingHom.comp_apply]
    rw [show (reesMap Φ (Localization.AtPrime 𝔪)) x = algebraMap R _ x from rfl]
    exact heq x
  set JV : MC (VLoc hpos) (D.n + 1) := ⟨vChart D.J.nonneg hd D.hwe hpos c' hF', pad (D.n + 1) D.J.e,
    hcentV, pad_nonneg' D.J.e D.J.nonneg, pad_antitone' D.J.nonneg D.J.anti⟩
  refine ⟨JV.mapRingEquiv (S' := Localization.AtPrime P₀) eq, ?_, rfl, ?_, ?_⟩
  · have := MC.Adm.mapRingEquiv (S' := Localization.AtPrime P₀) (J := JV) hadmV eq
    rwa [hweak] at this
  · have := IsInv.mapRingEquiv (S' := Localization.AtPrime P₀) hinvV eq
    rwa [hweak] at this
  · intro j hj f hf
    have h1 : (⟨LaurentPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) f) * T j,
        C_mul_T_mem_ReesAlg (Ideal.mem_map_of_mem _ hf)⟩ :
          ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) ∈
        (reesChart c' hF' D.J.nonneg hd D.hwe).RF (pad (D.n + 1) D.J.e) (1 / d) :=
      homog_mem_reesRF c' hF' D.J.nonneg hd D.hwe hj (Ideal.mem_map_of_mem _ hf)
    have h2 := Ideal.mem_map_of_mem (algebraMap (ReesAlg (Φ.loc (Localization.AtPrime 𝔪)))
      (VLoc hpos)) h1
    have hloc := Chart.localization_RF (S := VLoc hpos) (vertex hpos).primeCompl
      (reesChart c' hF' D.J.nonneg hd D.hwe) (pad (D.n + 1) D.J.e) (1 / d)
    rw [← hloc] at h2
    have h3 := Ideal.mem_map_of_mem eq h2
    rw [MC.mapRingEquiv_RF (S' := Localization.AtPrime P₀) (J := JV)]
    have hy : algebraMap R (Localization.AtPrime P₀) ⟨LaurentPolynomial.C f * T j,
        C_mul_T_mem_ReesAlg hf⟩ = eq (algebraMap (ReesAlg (Φ.loc (Localization.AtPrime 𝔪)))
          (VLoc hpos) ⟨LaurentPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) f) * T j,
            C_mul_T_mem_ReesAlg (Ideal.mem_map_of_mem _ hf)⟩) := by
      rw [← heq, ← hVR]
      congr 2
      apply Subtype.ext
      rw [reesMap_coe]
      exact lmap_C_mul_T _ _ _
    rw [hy]
    exact h3

end BezoutCounterexample.Principalization

