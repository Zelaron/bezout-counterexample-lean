import BezoutCounterexample.Principalization.Rees

/-!
# The invariant at the vertex of the weighted deformation

Part of the proof of Theorem 3.6 (`thm:drop`) of the paper.

* `truncW`, `MC.SA.toLex_le`, `MC.SA.RF_eq`: semi-associated centres bound all admissible centres.
* `weakIdeal`: the weak transform `(f Tᵈ : f ∈ I)`; `weak_le_reesRF`: it is admissible for the Rees
  centre of every compatible chart.
* `DE_stepA`, `DE_stepA'`, `DE_stepR`: one Method-1 step at `A_p` in a compatible chart
  initializes to a Method-1 step at the vertex in the Rees chart.
* `vertex_invariant` (**properties (D) and (E)**): at the vertex point, the weak transform has the
  same invariant as `I`, attained by the Rees centre of a compatible chart.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section Trunc

variable {n : ℕ}

/-- The first `j` weights of `e`, followed by zeros. -/
def truncW (e : Fin n → ℚ) (j : ℕ) : Fin n → ℚ := fun i => if (i : ℕ) < j then e i else 0

lemma truncW_nonneg {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (j : ℕ) : ∀ i, 0 ≤ truncW e j i :=
  fun i => by simp only [truncW]; split_ifs; exact he i; exact le_rfl

lemma truncW_antitone {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (j : ℕ) :
    Antitone (truncW e j) := by
  intro a b hab
  simp only [truncW]
  by_cases hb : (b : ℕ) < j
  · rw [if_pos hb, if_pos (lt_of_le_of_lt (Fin.le_def.1 hab) hb)]; exact hanti hab
  · rw [if_neg hb]; split_ifs; exact he a; exact le_rfl

lemma truncW_zero (e : Fin n → ℚ) : truncW e 0 = 0 := by funext i; simp [truncW]

lemma truncW_of_supp {e : Fin n → ℚ} {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) :
    truncW e k = e := by
  funext i
  simp only [truncW]
  split_ifs with h
  · rfl
  · by_contra h'; exact h ((hsupp i).1 (Ne.symm h'))

lemma nextE_truncW (e : Fin n → ℚ) {j : ℕ} (hj : j < n) :
    nextE (truncW e j) j (e ⟨j, hj⟩) = truncW e (j + 1) := by
  funext i
  simp only [nextE, truncW]
  by_cases h1 : (i : ℕ) < j
  · rw [if_pos h1, if_pos h1, if_pos (by omega)]
  · by_cases h2 : (i : ℕ) = j
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]; congr 1; exact Fin.ext h2.symm
    · rw [if_neg h1, if_neg h2, if_neg (by omega)]

lemma truncW_supp {e : Fin n → ℚ} {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) {j : ℕ}
    (hj : j ≤ k) : ∀ i, truncW e j i ≠ 0 ↔ (i : ℕ) < j := by
  intro i
  simp only [truncW]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => (hsupp i).2 (by omega)⟩
  · exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩

lemma lex_le_at {a b : Fin n → ℚ} (h : toLex a ≤ toLex b) {j : ℕ} (hj : j < n)
    (hagree : ∀ i : Fin n, (i : ℕ) < j → a i = b i) : a ⟨j, hj⟩ ≤ b ⟨j, hj⟩ := by
  by_contra hlt
  push_neg at hlt
  refine absurd h (not_le.2 ⟨⟨j, hj⟩, fun i hi => (hagree i (Fin.lt_def.1 hi)).symm, ?_⟩)
  simpa [Pi.toLex_apply] using hlt

end Trunc

section SALex

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

/-- A `k`-semi-associated centre bounds all admissible centres lexicographically from below. -/
lemma MC.SA.toLex_le {I : Ideal R} {k : ℕ} {J : MC R n} (hSA : MC.SA I k J) (J' : MC R n)
    (hJ' : J'.Adm I) : toLex J.e ≤ toLex J'.e := by
  rw [← not_lt]
  rintro ⟨i, hbelow, hlt⟩
  simp only [Pi.toLex_apply] at hbelow hlt
  by_cases hik : (i : ℕ) < k
  · exact absurd (hSA.max J' hJ' i hik fun i' hi' => hbelow i' hi') (not_le.2 hlt)
  · rw [hSA.e_eq_zero (by omega)] at hlt
    exact absurd (J'.nonneg i) (not_le.2 hlt)

/-- A `k`-semi-associated centre determines the weighted ideals of admissible centres with its
weights. -/
lemma MC.SA.RF_eq {I : Ideal R} {k : ℕ} {J : MC R n} (hSA : MC.SA I k J) (J' : MC R n)
    (hJ' : J'.Adm I) (he : J'.e = J.e) (t : ℚ) : J'.RF t = J.RF t := by
  obtain ⟨c'', -, hRF, hx⟩ := hSA.dom J' hJ' (fun i _ => by rw [he])
  rw [← hRF, he, MC.RF]
  exact Chart.RF_congr (fun i hi => hx i ((hSA.supp i).1 hi)) t

end SALex

section LocD

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] [Algebra R S]
  [IsScalarTower ℚ R S] (M : Submonoid R) [IsLocalization M S] {n : ℕ}

lemma Chart.localization_D (c : Chart R n) (β : Fin n →₀ ℕ) (r : R) :
    (c.localization (S := S) M).D β (algebraMap R S r) = algebraMap R S (c.D β r) := by
  induction β using Finsupp.induction_single with
  | h0 => simp [Chart.D_zero]
  | hs β i ih => rw [Chart.D_add_single, ih, Chart.localization_d, Chart.D_add_single]

lemma Chart.localization_Dv (c : Chart R n) (β : Fin n →₀ ℕ) (r : R) :
    (c.localization (S := S) M).Dv β (algebraMap R S r) = algebraMap R S (c.Dv β r) := by
  rw [Chart.Dv, Chart.Dv, c.localization_D M, map_rat_smul]

end LocD

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section Weak

variable {B : Type*} [CommRing B] [Algebra ℚ B] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}

/-- The weak transform `I_w = (f Tᵈ : f ∈ I)` in the Rees algebra. -/
def weakIdeal (I : Ideal B) (hId : I ≤ Φ.F d) : Ideal (ReesAlg Φ) :=
  Ideal.span (Set.range fun f : I =>
    (⟨LaurentPolynomial.C (f : B) * T d, C_mul_T_mem_ReesAlg (hId f.2)⟩ : ReesAlg Φ))

lemma chartFil_d (c : Chart B n) (hd : 0 < d) : chartFil c e d d = c.RF e 1 := by
  rw [chartFil, Int.cast_natCast, div_self (by exact_mod_cast hd.ne')]

lemma Chart.localization_RF {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    [Algebra R S] [IsScalarTower ℚ R S] (M : Submonoid R) [IsLocalization M S]
    (c : Chart R n) (e : Fin n → ℚ) (t : ℚ) :
    (c.localization (S := S) M).RF e t = (c.RF e t).map (algebraMap R S) := by
  rw [Chart.RF, Chart.RF, Ideal.map_span]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨α, h0, ht, rfl⟩
    exact ⟨_, ⟨α, h0, ht, rfl⟩, by simp [map_prod, map_pow]⟩
  · rintro ⟨_, ⟨α, h0, ht, rfl⟩, rfl⟩
    exact ⟨α, h0, ht, by simp [map_prod, map_pow]⟩

variable (he : ∀ i, 0 ≤ e i) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)

/-- The weak transform is admissible for the Rees centre of any compatible chart. -/
theorem weak_le_reesRF (c' : Chart B n) (hF' : ∀ j, Φ.F j = chartFil c' e d j) (I : Ideal B)
    (hId : I ≤ Φ.F d) :
    weakIdeal I hId ≤ (reesChart c' hF' he hd hw).RF (pad (n + 1) e) 1 := by
  classical
  rw [weakIdeal, Ideal.span_le]
  rintro _ ⟨⟨f, hf⟩, rfl⟩
  have hf1 : f ∈ c'.RF e 1 := by rw [← chartFil_d c' hd, ← hF']; exact hId hf
  show (⟨LaurentPolynomial.C f * T d, C_mul_T_mem_ReesAlg (hId hf)⟩ : ReesAlg Φ) ∈ _
  generalize C_mul_T_mem_ReesAlg (hId hf) = hmem
  revert hmem
  clear hf
  rw [Chart.RF] at hf1
  induction hf1 using Submodule.span_induction with
  | mem g hg =>
    intro hmem
    obtain ⟨α, hα0, hαt, rfl⟩ := hg
    have hwα := weight_ge_of_mem hd hw (show ((d : ℤ) : ℚ) / d ≤ lam e α by
      rw [Int.cast_natCast, div_self (by exact_mod_cast hd.ne')]; exact hαt)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (Finsupp.weight w α : ℤ) - d = m :=
      ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [rees_mono_eq c' hF' he hd hw α d m hm hmem]
    refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨pushIdx (Nat.le_succ n) α, ?_, ?_, ?_⟩)
    · intro i hi
      cases i using Fin.lastCases with
      | last => exact pushIdx_apply_ge _ _ _ (by simp)
      | cast a =>
        rw [← castLE_succ_eq, pushIdx_apply]
        rw [← castLE_succ_eq, pad_castLE] at hi
        exact hα0 a hi
    · rw [lam_pad]; exact hαt
    · rw [Fin.prod_univ_castSucc, pushIdx_apply_ge _ _ _ (by simp), pow_zero, mul_one]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← castLE_succ_eq, pushIdx_apply]; rfl
  | zero =>
    intro hmem
    have : (⟨_, hmem⟩ : ReesAlg Φ) = 0 := Subtype.ext (by simp)
    rw [this]; exact zero_mem _
  | add x y hx hy ihx ihy =>
    intro hmem
    have hxR : LaurentPolynomial.C x * T d ∈ ReesAlg Φ := C_mul_T_mem_ReesAlg (by
      rw [hF', chartFil_d c' hd, Chart.RF]; exact hx)
    have hyR : LaurentPolynomial.C y * T d ∈ ReesAlg Φ := C_mul_T_mem_ReesAlg (by
      rw [hF', chartFil_d c' hd, Chart.RF]; exact hy)
    have : (⟨_, hmem⟩ : ReesAlg Φ) = ⟨_, hxR⟩ + ⟨_, hyR⟩ :=
      Subtype.ext (by show LaurentPolynomial.C (x + y) * T d = _; rw [map_add, add_mul]; rfl)
    rw [this]; exact add_mem (ihx hxR) (ihy hyR)
  | smul a x hx ih =>
    intro hmem
    have hxR : LaurentPolynomial.C x * T d ∈ ReesAlg Φ := C_mul_T_mem_ReesAlg (by
      rw [hF', chartFil_d c' hd, Chart.RF]; exact hx)
    have : (⟨_, hmem⟩ : ReesAlg Φ) = algebraMap B (ReesAlg Φ) a * ⟨_, hxR⟩ :=
      Subtype.ext (by
        show LaurentPolynomial.C (a • x) * T d = _
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← LaurentPolynomial.C_eq_algebraMap,
          smul_eq_mul, map_mul, mul_assoc])
    rw [this]; exact Ideal.mul_mem_left _ _ (ih hxR)

end Weak

section Compat

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {Φ : WFil B}

/-- Compatibility with the filtration is preserved by Method-1 steps within a block of equal
weights. -/
lemma fcompat_nextChart (he : ∀ i, 0 ≤ e i) {c' : Chart B n} (hc' : c'.IsCentred)
    (hF' : ∀ m, Φ.F m = chartFil c' e d m) {jj l : Fin n} (hel : e l = e jj) (y : B) (u : Bˣ)
    (hu : c'.d l y = u) (hy : y ∈ maximalIdeal B) (hyRF : y ∈ c'.RF e (e l)) :
    ∀ m, Φ.F m = chartFil (nextChart c' jj l y u hu) e d m := by
  intro m
  rw [hF', chartFil, chartFil, nextChart, Chart.RF_reindex _ _ (fun i => by
      rcases eq_or_ne i jj with h | h
      · rw [h, Equiv.swap_apply_left, hel]
      · rcases eq_or_ne i l with h' | h'
        · rw [h', Equiv.swap_apply_right, hel]
        · rw [Equiv.swap_apply_of_ne_of_ne h h']),
    hc'.RF_replace he l y u hu hy hyRF]

end Compat

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section DE

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

/-- The local ring at the vertex. -/
abbrev VLoc (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B) :=
  Localization.AtPrime (vertex hpos)

theorem VLoc_noeth (c : Chart B n) (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i)
    (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i) : IsNoetherianRing (VLoc hpos) := by
  haveI := rees_noetherian c hF he hd hw
  exact IsLocalization.isNoetherianRing (vertex hpos).primeCompl _ inferInstance

/-- The Rees chart of a compatible chart, localized at the vertex. -/
def vChart (c' : Chart B n) (hF' : ∀ j, Φ.F j = chartFil c' e d j) : Chart (VLoc hpos) (n + 1) :=
  (reesChart c' hF' he hd hw).localization (vertex hpos).primeCompl

lemma vChart_isCentred (c' : Chart B n) (hF' : ∀ j, Φ.F j = chartFil c' e d j)
    (hc' : c'.IsCentred) : (vChart he hd hw hpos c' hF').IsCentred :=
  reesLoc_isCentred c' hF' he hd hw hc'

lemma pad_nonneg' (e : Fin n → ℚ) (he : ∀ i, 0 ≤ e i) : ∀ i, 0 ≤ pad (n + 1) e i := fun i => by
  simp only [pad]; split_ifs; exact he _; exact le_rfl

lemma pad_antitone' {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) :
    Antitone (pad (n + 1) e) := by
  intro a b hab
  simp only [pad]
  by_cases hb : (b : ℕ) < n
  · rw [dif_pos hb, dif_pos (lt_of_le_of_lt (Fin.le_def.1 hab) hb)]
    exact hanti (Fin.le_def.2 (by simpa using Fin.le_def.1 hab))
  · rw [dif_neg hb]; split_ifs; exact he _; exact le_rfl

end DE

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section DEA

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {Φ : WFil B}

/-- The A-side of a vertex step: Method 1 in a compatible chart has next weight `e_j`, and the
next coordinate can be chosen within the block of weight `e_j`. -/
theorem DE_stepA (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) {k : ℕ}
    (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) (I : Ideal B) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) {j : ℕ} (hjk : j < k) (hkn : k ≤ n)
    (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m)
    (hA : MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩) :
    ∃ (β₀ : Fin n →₀ ℕ) (f₀ : B) (hf₀ : f₀ ∈ I) (l : Fin n),
      coeff β₀ (c'.tau f₀) ≠ 0 ∧ lam (truncW e j) β₀ < 1 ∧ 0 < tailSum j β₀ ∧
      (∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (c'.tau g) ≠ 0) → lam (truncW e j) β < 1 →
        Xi (truncW e j) j β₀ ≤ Xi (truncW e j) j β) ∧
      j ≤ (l : ℕ) ∧ β₀ l ≠ 0 ∧ e l = e ⟨j, by omega⟩ ∧ lam e β₀ = 1 ∧
      nextW (truncW e j) j β₀ = e ⟨j, by omega⟩ := by
  classical
  have hjn : j < n := by omega
  set jj : Fin n := ⟨j, hjn⟩ with hjjdef
  have hej : 0 < e jj := lt_of_le_of_ne (he _) (Ne.symm ((hsupp jj).2 hjk))
  have hadm' : I ≤ c'.RF e 1 := by rw [← chartFil_d c' hd, ← hF']; exact hId
  set Jc : MC B n := ⟨c', e, hc', he, hanti⟩
  have hJc : Jc.Adm I := hadm'
  have hna : ¬ MC.Adm I ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩ := by
    intro hadm
    have h1 := hmax _ hadm
    have h2 := lex_le_at h1 hjn (fun i hi => by simp [truncW, hi])
    simp only [truncW, lt_irrefl, if_false] at h2
    exact absurd h2 (not_le.2 hej)
  obtain ⟨hj, β₀, f₀, hf₀, hf₀ne, hlt₀, hN₀, hmin₀, hnext₀, hbJ₀⟩ := hA.step_data hna
  set b := (1 - lam (truncW e j) β₀) / tailSum j β₀ with hbdef
  have hNq : (0 : ℚ) < tailSum j β₀ := by exact_mod_cast hN₀
  have hkey : lam (truncW e j) β₀ + b * tailSum j β₀ = 1 := by rw [hbdef]; field_simp; ring
  have hb_le : b ≤ e jj := (hnext₀ Jc hJc (fun i hi => by simp [Jc, truncW, hi])).2
  -- `b ≥ e_j` from maximality of `e`
  obtain ⟨l₀, hl₀, hβl₀⟩ := MC.tailSum_pos_exists hN₀
  have hb_ge : e jj ≤ b := by
    obtain ⟨hj2, hun2, hb2, u, hu, hc2, hnn2, ha2, hSA2⟩ :=
      hA.step_run_of hna β₀ f₀ hf₀ hf₀ne hlt₀ hN₀ hmin₀ l₀ hl₀ hβl₀
    obtain ⟨J'', hJ'', hag''⟩ := hSA2.dom0
    have h1 := hmax J'' hJ''
    have h2 := lex_le_at h1 hjn (fun i hi => by
      rw [hag'' i (by omega)]
      simp [nextE, truncW, hi])
    rw [hag'' jj (by simp [hjjdef])] at h2
    simpa [nextE, nextW, hjjdef] using h2
  have hbeq : b = e jj := le_antisymm hb_le hb_ge
  -- `λ_e(β₀) ≥ 1` by duality
  have hlam1 : 1 ≤ lam e β₀ := by
    by_contra h; push_neg at h
    exact hf₀ne ((hc'.mem_RF_iff he 1 f₀).1 (hadm' hf₀) β₀ h)
  -- splitting `λ_e(β₀)` at `j`
  have hsum : lam e β₀ = lam (truncW e j) β₀ +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) * e i := by
    simp only [lam, truncW]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < j),
        (β₀ i : ℚ) * (if (i : ℕ) < j then e i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_filter] at hi; rw [if_neg hi.2, mul_zero]
    have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j),
        (β₀ i : ℚ) * (if (i : ℕ) < j then e i else 0) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), (β₀ i : ℚ) * e i :=
      Finset.sum_congr rfl fun i hi => by rw [Finset.mem_filter] at hi; rw [if_pos hi.2]
    rw [h1, h2, add_zero]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i; simp
  have htail : (tailSum j β₀ : ℚ) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) := by
    simp [tailSum]
  have hle : ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) * e i ≤
      e jj * tailSum j β₀ := by
    rw [htail, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hanti (show jj ≤ i from Fin.le_def.2 (by
      simp only [hjjdef]; exact hi.2))) (Nat.cast_nonneg _)
  have hsplit : ∀ l : Fin n, j ≤ (l : ℕ) → β₀ l ≠ 0 → e l = e jj := by
    intro l hl hβl
    by_contra hne
    have hlt : e l < e jj := lt_of_le_of_ne (hanti (Fin.le_def.2 (by simp [hjjdef]; omega))) hne
    have hless : ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) * e i <
        e jj * tailSum j β₀ := by
      rw [htail, Finset.mul_sum]
      apply Finset.sum_lt_sum
      · intro i hi
        rw [Finset.mem_filter] at hi
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hanti (show jj ≤ i from Fin.le_def.2 (by
          simp only [hjjdef]; exact hi.2))) (Nat.cast_nonneg _)
      · refine ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩, ?_⟩
        rw [mul_comm]
        exact mul_lt_mul_of_pos_right hlt
          (show (0 : ℚ) < (β₀ l : ℚ) by exact_mod_cast Nat.pos_of_ne_zero hβl)
    have : lam e β₀ < 1 := by rw [hsum, ← hkey, hbeq]; linarith
    linarith
  obtain ⟨l, hl, hβl⟩ := MC.tailSum_pos_exists hN₀
  have hel := hsplit l hl hβl
  have hlam : lam e β₀ = 1 := by
    refine le_antisymm ?_ hlam1
    rw [hsum, ← hkey, hbeq]; linarith
  refine ⟨β₀, f₀, hf₀, l, hf₀ne, hlt₀, hN₀, hmin₀, hl, hβl, hel, hlam, ?_⟩
  rw [nextW]; exact hbeq

end DEA

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section ReesDv

variable {B : Type*} [CommRing B] [Algebra ℚ B] {n : ℕ}
variable (c : Chart B n) {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ}
  {Φ : WFil B} (hF : ∀ j, Φ.F j = chartFil c e d j) (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i)

theorem reesChart_Dv_hom (γ : Fin n →₀ ℕ) (f : B) (j : ℤ)
    (h : LaurentPolynomial.C f * T j ∈ ReesAlg Φ) :
    (((reesChart c hF he hd hw).Dv (pushIdx (Nat.le_succ n) γ) ⟨_, h⟩ : ReesAlg Φ) : B[T;T⁻¹]) =
      LaurentPolynomial.C (c.Dv γ f) * T (j - Finsupp.weight w γ) := by
  rw [Chart.Dv, fact_push, Algebra.smul_def, Subalgebra.coe_mul, reesChart_D_hom, Chart.Dv,
    map_rat_smul, Algebra.smul_def, mul_assoc]
  rfl

end ReesDv

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section DEStep

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

lemma swap_castSucc_eq {n : ℕ} (a b i : Fin n) :
    Equiv.swap (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc i) =
      Fin.castSucc (Equiv.swap a b i) := by
  have := swap_castLE (Nat.le_succ n) a b i
  simpa [castLE_succ_eq] using this

lemma swap_castSucc_last {n : ℕ} (a b : Fin n) :
    Equiv.swap (Fin.castSucc a) (Fin.castSucc b) (Fin.last n) = Fin.last n :=
  Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last a).ne' (Fin.castSucc_lt_last b).ne'

include hd in
/-- The A-side data of a vertex step, with the chart after the step. -/
theorem DE_stepA' {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) (I : Ideal B)
    (hId : I ≤ Φ.F d) (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) {j : ℕ}
    (hjk : j < k) (hkn : k ≤ n)
    (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m)
    (hA : MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩) :
    ∃ (β₀ : Fin n →₀ ℕ) (f₀ : B) (hf₀ : f₀ ∈ I) (l : Fin n) (hl : j ≤ (l : ℕ)) (hβl : β₀ l ≠ 0)
      (u : Bˣ) (hu : c'.d l (c'.Dv (β₀ - Finsupp.single l 1) f₀) = u)
      (hc'' : (nextChart c' ⟨j, by omega⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu).IsCentred),
      IsUnit (c'.D β₀ f₀) ∧ coeff β₀ (c'.tau f₀) ≠ 0 ∧ lam (truncW e j) β₀ < 1 ∧
      0 < tailSum j β₀ ∧ e l = e ⟨j, by omega⟩ ∧ lam e β₀ = 1 ∧
      nextW (truncW e j) j β₀ = e ⟨j, by omega⟩ ∧
      (∀ m, Φ.F m = chartFil (nextChart c' ⟨j, by omega⟩ l
        (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu) e d m) ∧
      MC.SA I (j + 1) ⟨nextChart c' ⟨j, by omega⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu,
        truncW e (j + 1), hc'', truncW_nonneg he _, truncW_antitone he hanti _⟩ := by
  have hjn : j < n := by omega
  obtain ⟨β₀, f₀, hf₀, l, hf₀ne, hlt₀, hN₀, hmin₀, hl, hβl, hel, hlam, hW⟩ :=
    DE_stepA he hanti hd hsupp I hId hmax hjk hkn c' hc' hF' hA
  have hej : 0 < e ⟨j, hjn⟩ := lt_of_le_of_ne (he _) (Ne.symm ((hsupp _).2 hjk))
  have hna : ¬ MC.Adm I ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩ := by
    intro hadm
    have h1 := hmax _ hadm
    have h2 := lex_le_at h1 hjn (fun i hi => by simp [truncW, hi])
    simp only [truncW, lt_irrefl, if_false] at h2
    exact absurd h2 (not_le.2 hej)
  obtain ⟨hj', hunit, hbJ, u, hu, hc'', hnn'', ha'', hSA''⟩ :=
    hA.step_run_of hna β₀ f₀ hf₀ hf₀ne hlt₀ hN₀ hmin₀ l hl hβl
  have hwts : nextE (truncW e j) j (nextW (truncW e j) j β₀) = truncW e (j + 1) := by
    rw [hW]; exact nextE_truncW e hjn
  have hf1 : f₀ ∈ c'.RF e 1 := by rw [← chartFil_d c' hd, ← hF']; exact hId hf₀
  have hyRF : c'.Dv (β₀ - Finsupp.single l 1) f₀ ∈ c'.RF e (e l) := by
    have hlow := Chart.Dv_mem_RF_of_lowersBy c' c' e e (fun i => c'.lowersBy_self he i)
      (β₀ - Finsupp.single l 1) hf1
    have hlamsub : lam e (β₀ - Finsupp.single l 1) = lam e β₀ - e l := by
      have h := congrArg (lam e) (MC.add_single_sub hβl)
      rw [lam_add, lam_single] at h
      push_cast at h; linarith
    rw [hlamsub, hlam] at hlow
    simpa using hlow
  have hel' : 0 < e l := by rw [hel]; exact hej
  have hy := hc'.RF_le_maximalIdeal hel' hyRF
  refine ⟨β₀, f₀, hf₀, l, hl, hβl, u, hu, hc'', hunit, hf₀ne, hlt₀, hN₀, hel, hlam, hW,
    fcompat_nextChart he hc' hF' hel _ u hu hy hyRF, ?_⟩
  have hMC : (⟨nextChart c' ⟨j, hj'⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu,
      nextE (truncW e j) j (nextW (truncW e j) j β₀), hc'', hnn'', ha''⟩ : MC B n) =
      ⟨nextChart c' ⟨j, hj'⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu,
        truncW e (j + 1), hc'', truncW_nonneg he _, truncW_antitone he hanti _⟩ :=
    MC.ext' rfl hwts
  rw [hMC] at hSA''
  exact hSA''

end DEStep

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section DEStepR

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

/-- The weak transform at the vertex. -/
abbrev weakV (I : Ideal B) (hId : I ≤ Φ.F d) : Ideal (VLoc hpos) :=
  (weakIdeal I hId).map (algebraMap (ReesAlg Φ) (VLoc hpos))

lemma pad_zero_ge_truncW {j : ℕ} (e : Fin n → ℚ) :
    ∀ i : Fin (n + 1), j ≤ (i : ℕ) → pad (n + 1) (truncW e j) i = 0 := by
  intro i hi
  simp only [pad, truncW]
  split_ifs with h1 h2
  · exact absurd h2 (by simp; omega)
  · rfl
  · rfl

omit [IsLocalRing B] [IsNoetherianRing B] in
lemma nextChart_x_apply {S : Type*} [CommRing S] [Algebra ℚ S] {m : ℕ} (c : Chart S m)
    (jj l : Fin m) (g : S) (u : Sˣ) (hu : c.d l g = u) (i : Fin m) :
    (nextChart c jj l g u hu).x i = if Equiv.swap jj l i = l then g else c.x (Equiv.swap jj l i) := by
  simp only [nextChart, Chart.reindex_x]
  split_ifs with h
  · rw [h, Chart.replace_x_self]
  · rw [Chart.replace_x_ne _ _ _ _ _ h]

set_option maxHeartbeats 1000000 in
theorem DE_stepR (c₀ : Chart B n) (hF₀ : ∀ m, Φ.F m = chartFil c₀ e d m) {k : ℕ}
    (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) (hkn : k ≤ n) (I : Ideal B) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) {j : ℕ} (hjk : j < k)
    (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m)
    (hA : MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩)
    (hR : MC.SA (weakV hpos I hId) j ⟨vChart he hd hw hpos c' hF', pad (n + 1) (truncW e j),
        vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' _ (truncW_nonneg he j),
        pad_antitone' (truncW_nonneg he j) (truncW_antitone he hanti j)⟩) :
    ∃ (c'' : Chart B n) (hc'' : c''.IsCentred) (hF'' : ∀ m, Φ.F m = chartFil c'' e d m),
      MC.SA I (j + 1) ⟨c'', truncW e (j + 1), hc'', truncW_nonneg he _,
        truncW_antitone he hanti _⟩ ∧
      MC.SA (weakV hpos I hId) (j + 1) ⟨vChart he hd hw hpos c'' hF'',
          pad (n + 1) (truncW e (j + 1)), vChart_isCentred he hd hw hpos c'' hF'' hc'',
          pad_nonneg' _ (truncW_nonneg he _),
          pad_antitone' (truncW_nonneg he _) (truncW_antitone he hanti _)⟩ := by
  classical
  haveI := VLoc_noeth hpos c₀ hF₀ he hd hw
  have hjn : j < n := by omega
  obtain ⟨β₀, f₀, hf₀, l, hl, hβl, u, hu, hc'', hunit, hf₀ne, hlt₀, hN₀, hel, hlam, hW, hF'',
    hSA''⟩ := DE_stepA' he hanti hd hsupp I hId hmax hjk hkn c' hc' hF' hA
  refine ⟨_, hc'', hF'', hSA'', ?_⟩
  set Rc := vChart he hd hw hpos c' hF' with hRcdef
  have hRc : Rc.IsCentred := vChart_isCentred he hd hw hpos c' hF' hc'
  have hf₀d : LaurentPolynomial.C f₀ * T d ∈ ReesAlg Φ := C_mul_T_mem_ReesAlg (hId hf₀)
  set F₀ : VLoc hpos := algebraMap (ReesAlg Φ) (VLoc hpos) ⟨_, hf₀d⟩ with hF₀def
  have hF₀mem : F₀ ∈ weakV hpos I hId :=
    Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨f₀, hf₀⟩, rfl⟩)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hlamw : lam e β₀ = (Finsupp.weight w β₀ : ℚ) / d := by
    rw [lam, Finsupp.weight_eq_sum, eq_div_iff hdq.ne']
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Nat.cast_mul, hw i]; ring
  have hweight : (Finsupp.weight w β₀ : ℤ) = d := by
    rw [hlam, eq_comm, div_eq_one_iff_eq hdq.ne'] at hlamw
    exact_mod_cast hlamw
  have hDF : Rc.D (pushIdx (Nat.le_succ n) β₀) F₀ =
      algebraMap (ReesAlg Φ) (VLoc hpos) (algebraMap B (ReesAlg Φ) (c'.D β₀ f₀)) := by
    rw [hRcdef, vChart, hF₀def, Chart.localization_D]
    congr 1
    apply Subtype.ext
    rw [reesChart_D_hom, hweight, sub_self, T_zero, mul_one, Subalgebra.coe_algebraMap,
      ← LaurentPolynomial.C_eq_algebraMap]
  have hunitR : IsUnit (Rc.D (pushIdx (Nat.le_succ n) β₀) F₀) := by
    rw [hDF]; exact (hunit.map _).map _
  have hfneR : coeff (pushIdx (Nat.le_succ n) β₀) (Rc.tau F₀) ≠ 0 := by
    rw [Ne, Chart.coeff_tau_eq_zero_iff, Chart.Dv, Algebra.smul_def]
    intro hmem
    have hq : IsUnit (algebraMap ℚ (VLoc hpos)
        ((∏ i, ((pushIdx (Nat.le_succ n) β₀) i).factorial : ℕ) : ℚ)⁻¹) :=
      (isUnit_iff_ne_zero.2 (by positivity)).map _
    exact (IsLocalRing.notMem_maximalIdeal.2 hunitR) ((Ideal.unit_mul_mem_iff_mem _ hq).1 hmem)
  have hltR : lam (pad (n + 1) (truncW e j)) (pushIdx (Nat.le_succ n) β₀) < 1 := by
    rw [lam_pad]; exact hlt₀
  have hNR : 0 < tailSum j (pushIdx (Nat.le_succ n) β₀) := by rw [tailSum_push]; exact hN₀
  have hnaR : ¬ MC.Adm (weakV hpos I hId) ⟨Rc, pad (n + 1) (truncW e j), hRc,
      pad_nonneg' _ (truncW_nonneg he j),
      pad_antitone' (truncW_nonneg he j) (truncW_antitone he hanti j)⟩ := by
    intro hadm
    exact hfneR ((hRc.mem_RF_iff (pad_nonneg' _ (truncW_nonneg he j)) 1 F₀).1 (hadm hF₀mem)
      _ hltR)
  have hJV : weakV hpos I hId ≤ Rc.RF (pad (n + 1) e) 1 := by
    rw [hRcdef, vChart, Chart.localization_RF]
    exact Ideal.map_mono (weak_le_reesRF he hd hw c' hF' I hId)
  have hjR : j < n + 1 := by omega
  have hej : 0 < e ⟨j, hjn⟩ := lt_of_le_of_ne (he _) (Ne.symm ((hsupp _).2 hjk))
  have hejR : pad (n + 1) e ⟨j, hjR⟩ = e ⟨j, hjn⟩ := by simp [pad, hjn]
  have hcompl := hR.compl_adm ⟨Rc, pad (n + 1) e, hRc, pad_nonneg' e he, pad_antitone' he hanti⟩
    hJV (fun i hi => by
      show pad (n + 1) e i = pad (n + 1) (truncW e j) i
      simp only [pad, truncW]
      split_ifs <;> first | rfl | (exfalso; simp_all; omega)) hjR (by
      show 0 < pad (n + 1) e ⟨j, hjR⟩
      rw [hejR]; exact hej)
  have hW' : 1 - lam (truncW e j) β₀ = e ⟨j, hjn⟩ * tailSum j β₀ := by
    have hNq : (0 : ℚ) < tailSum j β₀ := by exact_mod_cast hN₀
    rw [nextW] at hW
    rw [← hW]; field_simp
  have hminR : ∀ β' : Fin (n + 1) →₀ ℕ, (∃ g ∈ weakV hpos I hId, coeff β' (Rc.tau g) ≠ 0) →
      lam (pad (n + 1) (truncW e j)) β' < 1 →
      Xi (pad (n + 1) (truncW e j)) j (pushIdx (Nat.le_succ n) β₀) ≤
        Xi (pad (n + 1) (truncW e j)) j β' := by
    rintro β' ⟨g, hg, hgne⟩ hβ'
    have h1 := hcompl hg
    have hcnn : ∀ i, 0 ≤ compl (pad (n + 1) (truncW e j)) j (pad (n + 1) e ⟨j, hjR⟩) i := by
      intro i; simp only [compl]; split_ifs
      · exact pad_nonneg' _ (truncW_nonneg he j) i
      · rw [hejR]; exact hej.le
    have h2 : 1 ≤ lam (compl (pad (n + 1) (truncW e j)) j (pad (n + 1) e ⟨j, hjR⟩)) β' := by
      by_contra h; push_neg at h
      exact hgne ((hRc.mem_RF_iff hcnn 1 g).1 h1 β' h)
    rw [lam_compl (pad_zero_ge_truncW e), hejR] at h2
    simp only [Xi]
    rw [tailSum_push, lam_pad]
    have hNq : (0 : ℚ) < tailSum j β₀ := by exact_mod_cast hN₀
    have hp1 : 0 < 1 - lam (truncW e j) β₀ := by linarith
    have hp2 : 0 < 1 - lam (pad (n + 1) (truncW e j)) β' := by linarith
    rw [div_le_div_iff₀ hp1 hp2, hW']
    have : (1 - lam (pad (n + 1) (truncW e j)) β') ≤ e ⟨j, hjn⟩ * tailSum j β' := by linarith
    nlinarith
  obtain ⟨hjR', hunitR', hbJR, uR, huR, hcR, hnnR, haR, hSAR⟩ :=
    hR.step_run_of hnaR (pushIdx (Nat.le_succ n) β₀) F₀ hF₀mem hfneR hltR hNR hminR
      (Fin.castSucc l) (by simpa using hl) (by rw [← castLE_succ_eq, pushIdx_apply]; exact hβl)
  have hwl : w l = w ⟨j, hjn⟩ := by
    have h1 := hw l; have h2 := hw ⟨j, hjn⟩; rw [hel] at h1; exact_mod_cast h1.trans h2.symm
  have hwswap : ∀ a, w (Equiv.swap ⟨j, hjn⟩ l a) = w a := by
    intro a
    rcases eq_or_ne a ⟨j, hjn⟩ with h | h
    · rw [h, Equiv.swap_apply_left, hwl]
    · rcases eq_or_ne a l with h' | h'
      · rw [h', Equiv.swap_apply_right, hwl]
      · rw [Equiv.swap_apply_of_ne_of_ne h h']
  have hgR : Rc.Dv (pushIdx (Nat.le_succ n) β₀ - Finsupp.single (Fin.castSucc l) 1) F₀ =
      algebraMap (ReesAlg Φ) (VLoc hpos) ((reesChart c' hF' he hd hw).Dv
        (pushIdx (Nat.le_succ n) (β₀ - Finsupp.single l 1)) ⟨_, hf₀d⟩) := by
    rw [← castLE_succ_eq, ← pushIdx_sub_single, hRcdef, vChart, hF₀def, Chart.localization_Dv]
  have hsplitw : Finsupp.weight w β₀ = Finsupp.weight w (β₀ - Finsupp.single l 1) + w l := by
    conv_lhs => rw [← MC.add_single_sub hβl]
    rw [map_add, Finsupp.weight_single, smul_eq_mul, one_mul]
  have hgcoe : (((reesChart c' hF' he hd hw).Dv (pushIdx (Nat.le_succ n) (β₀ - Finsupp.single l 1))
      ⟨_, hf₀d⟩ : ReesAlg Φ) : B[T;T⁻¹]) =
      LaurentPolynomial.C (c'.Dv (β₀ - Finsupp.single l 1) f₀) * T (w l) := by
    rw [reesChart_Dv_hom]
    congr 2
    have := hweight
    rw [hsplitw] at this
    push_cast at this
    omega
  have hjj : (⟨j, hjR'⟩ : Fin (n + 1)) = Fin.castSucc ⟨j, hjn⟩ := rfl
  set gR := Rc.Dv (pushIdx (Nat.le_succ n) β₀ - Finsupp.single (Fin.castSucc l) 1) F₀
    with hgRdef
  set c'' := nextChart c' ⟨j, hjn⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu with hc''def
  have hc''x : ∀ a, c''.x a = if Equiv.swap ⟨j, hjn⟩ l a = l then
      c'.Dv (β₀ - Finsupp.single l 1) f₀ else c'.x (Equiv.swap ⟨j, hjn⟩ l a) :=
    fun a => nextChart_x_apply c' _ _ _ _ _ a
  have hgR' : gR = algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c'' hF'' he hd hw
      (Fin.castSucc ⟨j, hjn⟩)) := by
    rw [hgR]
    congr 1
    apply Subtype.ext
    rw [hgcoe, reesX_castSucc, hc''x, if_pos (Equiv.swap_apply_left _ _), hwl]
  have heqchart : nextChart Rc ⟨j, hjR'⟩ (Fin.castSucc l) gR uR huR =
      vChart he hd hw hpos c'' hF'' := by
    apply Chart.eq_of_x
    funext i
    rw [nextChart_x_apply, hjj]
    cases i using Fin.lastCases with
    | last =>
      rw [swap_castSucc_last, if_neg (Fin.castSucc_lt_last l).ne']
      show algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c' hF' he hd hw (Fin.last n)) =
        algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c'' hF'' he hd hw (Fin.last n))
      congr 1
      apply Subtype.ext
      rw [reesX_last, reesX_last]
    | cast a =>
      rw [swap_castSucc_eq]
      by_cases hb : Equiv.swap ⟨j, hjn⟩ l a = l
      · rw [if_pos (congrArg Fin.castSucc hb), hgR']
        have ha : a = ⟨j, hjn⟩ := by
          have := congrArg (Equiv.swap ⟨j, hjn⟩ l) hb
          rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
        subst ha
        rfl
      · rw [if_neg (fun h => hb (Fin.castSucc_injective _ h))]
        show algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c' hF' he hd hw _) =
          algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c'' hF'' he hd hw (Fin.castSucc a))
        congr 1
        apply Subtype.ext
        rw [reesX_castSucc, reesX_castSucc, hc''x, if_neg hb, hwswap]
  have hwtsR : nextE (pad (n + 1) (truncW e j)) j
      (nextW (pad (n + 1) (truncW e j)) j (pushIdx (Nat.le_succ n) β₀)) =
      pad (n + 1) (truncW e (j + 1)) := by
    have : nextW (pad (n + 1) (truncW e j)) j (pushIdx (Nat.le_succ n) β₀) =
        nextW (truncW e j) j β₀ := by simp only [nextW, lam_pad, tailSum_push]
    rw [this, hW, ← pad_nextE hjn, nextE_truncW e hjn]
  have hMC : (⟨_, _, hcR, hnnR, haR⟩ : MC (VLoc hpos) (n + 1)) =
      ⟨vChart he hd hw hpos _ hF'', pad (n + 1) (truncW e (j + 1)),
        vChart_isCentred he hd hw hpos _ hF'' hc'', pad_nonneg' _ (truncW_nonneg he _),
        pad_antitone' (truncW_nonneg he _) (truncW_antitone he hanti _)⟩ :=
    MC.ext' heqchart hwtsR
  rw [hMC] at hSAR
  exact hSAR

end DEStepR

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section DEMain

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B]
  {n : ℕ} {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

omit [IsNoetherianRing B] in
lemma reesAlg_isDomain : IsDomain (ReesAlg Φ) := inferInstance

include hd in
lemma weakV_ne_bot (c₀ : Chart B n) (hF₀ : ∀ m, Φ.F m = chartFil c₀ e d m) (he : ∀ i, 0 ≤ e i)
    (hw : ∀ i, (w i : ℚ) = d * e i) (I : Ideal B) (hI0 : I ≠ ⊥) (hId : I ≤ Φ.F d) :
    weakV hpos I hId ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  intro h
  have hmem : algebraMap (ReesAlg Φ) (VLoc hpos) ⟨_, C_mul_T_mem_ReesAlg (hId hf)⟩ ∈
      weakV hpos I hId := Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨f, hf⟩, rfl⟩)
  rw [h, Ideal.mem_bot] at hmem
  have hinj := IsLocalization.injective (VLoc hpos)
    (Ideal.primeCompl_le_nonZeroDivisors (vertex hpos))
  have h2 := hinj (hmem.trans (map_zero _).symm)
  have h3 := congrArg (fun p : ReesAlg Φ => (p : B[T;T⁻¹]).coeff d) h2
  simp only [coeff_C_mul_T, if_pos rfl] at h3
  exact hf0 (by simpa using h3)

lemma weakV_le_max (I : Ideal B) (hId : I ≤ Φ.F d) (hd : 0 < d) :
    weakV hpos I hId ≤ maximalIdeal (VLoc hpos) := by
  rw [weakV, Ideal.map_le_iff_le_comap, weakIdeal, Ideal.span_le]
  rintro _ ⟨⟨f, hf⟩, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (VLoc hpos) (vertex hpos), mem_vertex]
  show (LaurentPolynomial.C f * T d).coeff 0 ∈ maximalIdeal B
  rw [coeff_C_mul_T, if_neg (by omega)]
  exact zero_mem _

end DEMain

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries

section DEMain2

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B]
  {n : ℕ} {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

/-- **The invariant at the vertex** (Brais, properties (D) and (E)): at the vertex point of the
weighted deformation, the weak transform has the same invariant as `I`, and its maximal centre is
the Rees centre of a compatible chart. -/
theorem vertex_invariant (c₀ : Chart B n) (hc₀ : c₀.IsCentred)
    (hF₀ : ∀ m, Φ.F m = chartFil c₀ e d m) {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)
    (hkn : k ≤ n) (I : Ideal B) (hI0 : I ≠ ⊥) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) :
    ∃ (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m),
      MC.SA (weakV hpos I hId) k ⟨vChart he hd hw hpos c' hF', pad (n + 1) e,
        vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' e he, pad_antitone' he hanti⟩ := by
  haveI := VLoc_noeth hpos c₀ hF₀ he hd hw
  have hIm : I ≤ maximalIdeal B := hId.trans (hpos d (by exact_mod_cast hd))
  have key : ∀ j, j ≤ k → ∃ (c' : Chart B n) (hc' : c'.IsCentred)
      (hF' : ∀ m, Φ.F m = chartFil c' e d m),
      MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩ ∧
      MC.SA (weakV hpos I hId) j ⟨vChart he hd hw hpos c' hF', pad (n + 1) (truncW e j),
        vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' _ (truncW_nonneg he j),
        pad_antitone' (truncW_nonneg he j) (truncW_antitone he hanti j)⟩ := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨c₀, hc₀, hF₀, ?_, ?_⟩
      · have h := MC.sa_zero hI0 hIm c₀ hc₀
        have hMC : (⟨c₀, 0, hc₀, fun _ => le_rfl, fun _ _ _ => le_rfl⟩ : MC B n) =
            ⟨c₀, truncW e 0, hc₀, truncW_nonneg he 0, truncW_antitone he hanti 0⟩ :=
          MC.ext' rfl (truncW_zero e).symm
        rwa [hMC] at h
      · have h := MC.sa_zero (weakV_ne_bot hd hpos c₀ hF₀ he hw I hI0 hId)
          (weakV_le_max hpos I hId hd) (vChart he hd hw hpos c₀ hF₀)
          (vChart_isCentred he hd hw hpos c₀ hF₀ hc₀)
        have hMC : (⟨vChart he hd hw hpos c₀ hF₀, 0, vChart_isCentred he hd hw hpos c₀ hF₀ hc₀,
            fun _ => le_rfl, fun _ _ _ => le_rfl⟩ : MC (VLoc hpos) (n + 1)) =
            ⟨vChart he hd hw hpos c₀ hF₀, pad (n + 1) (truncW e 0),
              vChart_isCentred he hd hw hpos c₀ hF₀ hc₀, pad_nonneg' _ (truncW_nonneg he 0),
              pad_antitone' (truncW_nonneg he 0) (truncW_antitone he hanti 0)⟩ :=
          MC.ext' rfl (by
            show (0 : Fin (n + 1) → ℚ) = pad (n + 1) (truncW e 0)
            rw [truncW_zero, pad_zero'])
        rwa [hMC] at h
    | succ j ih =>
      intro hj
      obtain ⟨c', hc', hF', hA, hR⟩ := ih (by omega)
      exact DE_stepR he hanti hd hw hpos c₀ hF₀ hsupp hkn I hId hmax (by omega) c' hc' hF' hA hR
  obtain ⟨c', hc', hF', -, hR⟩ := key k le_rfl
  refine ⟨c', hc', hF', ?_⟩
  have hMC : (⟨vChart he hd hw hpos c' hF', pad (n + 1) (truncW e k),
      vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' _ (truncW_nonneg he k),
      pad_antitone' (truncW_nonneg he k) (truncW_antitone he hanti k)⟩ : MC (VLoc hpos) (n + 1)) =
      ⟨vChart he hd hw hpos c' hF', pad (n + 1) e, vChart_isCentred he hd hw hpos c' hF' hc',
        pad_nonneg' e he, pad_antitone' he hanti⟩ :=
    MC.ext' rfl (by
      show pad (n + 1) (truncW e k) = pad (n + 1) e
      rw [truncW_of_supp hsupp])
  rwa [hMC] at hR

end DEMain2

end BezoutCounterexample.Principalization

