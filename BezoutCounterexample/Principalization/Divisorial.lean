import BezoutCounterexample.Principalization.TorsorDer

/-!
# The divisorial case (`k = 1`)

Lemma 4.1 (`lem:divisorial`) of the paper.

If the maximal invariant has length one, the component is a prime divisor `𝔭 = (π)`
(`div_eq_span`), `I ⊆ (π^a)` (`div_le_span_pow`), and the colon ideal `I : π^a` has no zeros on
`V(π)` (`div_not_mem`); its invariants are those of `I`, the number of components drops
(`div_count`), and the length-bound data pass to it (`div_vertOK`, `div_dimOK`).
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section OrderBound

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}

/-- Powers of the maximal ideal lie in the constant-weight monomial ideals. -/
lemma pow_max_le_RF_const {c : Chart S n} (hc : c.IsCentred) {w : ℚ} (hw : 0 < w) (j : ℕ) :
    maximalIdeal S ^ j ≤ c.RF (fun _ => w) (j * w) := by
  induction j with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, c.RF_of_nonpos (fun _ => hw.le) le_rfl]
    exact le_top
  | succ j ih =>
    rw [pow_succ]
    have hmax : maximalIdeal S ≤ c.RF (fun _ => w) w := by
      rw [hc, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact c.x_mem_RF (fun _ => w) i hw.ne'
    refine (Ideal.mul_mono ih hmax).trans ?_
    have := c.RF_mul_le (fun _ => w) (j * w) w
    rwa [show (j : ℚ) * w + w = ((j + 1 : ℕ) : ℚ) * w by push_cast; ring] at this

/-- **An order bound bounds the first weight of the invariant.** -/
lemma IsInv.zero_le_of_le_pow {I : Ideal S} {e : Fin n → ℚ} (he : IsInv I n e)
    (c : Chart S n) (hc : c.IsCentred) {b : ℕ} (hb : 0 < b) (hIb : I ≤ maximalIdeal S ^ b)
    (h0 : 0 < n) : e ⟨0, h0⟩ ≤ 1 / b := by
  have hw : (0 : ℚ) < 1 / b := by positivity
  set J' : MC S n := ⟨c, fun _ => 1 / b, hc, fun _ => hw.le, fun _ _ _ => le_rfl⟩
  have hadm : J'.Adm I := by
    show I ≤ c.RF (fun _ => 1 / b) 1
    have := pow_max_le_RF_const hc hw b
    rw [show (b : ℚ) * (1 / b) = 1 by field_simp] at this
    exact hIb.trans this
  have := he.2 J' hadm
  exact lex_le_at this h0 (fun i hi => absurd hi (Nat.not_lt_zero _))

end OrderBound

section Global

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

lemma invAt_zero_le_of_le_pow {I : Ideal A} {𝔪 : Ideal A} [𝔪.IsMaximal] {v : ℕ → ℚ}
    (hv : InvAt I 𝔪 v) {b : ℕ} (hb : 0 < b) (hIb : I ≤ 𝔪 ^ b) : v 0 ≤ 1 / b := by
  obtain ⟨n, e, he, rfl⟩ := hv
  by_cases h0 : 0 < n
  · simp only [ext0, dif_pos h0]
    obtain ⟨J, -, -⟩ := he.1
    refine he.zero_le_of_le_pow J.c J.centred hb ?_ h0
    rw [Iloc, ← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 (Localization.AtPrime 𝔪),
      ← Ideal.map_pow]
    exact Ideal.map_mono hIb
  · simp only [ext0, dif_neg h0]; positivity

/-- A prime which is locally principal at a point and contains a prime element is principal. -/
lemma eq_span_of_loc_principal {𝔭 𝔪 : Ideal A} [𝔭.IsPrime] [𝔪.IsPrime] (h𝔭𝔪 : 𝔭 ≤ 𝔪)
    {π : A} (hπ : Prime π) (hπ𝔭 : π ∈ 𝔭) {x : Localization.AtPrime 𝔪}
    (hx : x ∈ maximalIdeal (Localization.AtPrime 𝔪))
    (hloc : 𝔭.map (algebraMap A (Localization.AtPrime 𝔪)) = Ideal.span {x}) :
    𝔭 = Ideal.span {π} := by
  have hπ𝔪 : π ∈ 𝔪 := h𝔭𝔪 hπ𝔭
  haveI hπp : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hdisj : Disjoint (𝔪.primeCompl : Set A) (Ideal.span {π} : Set A) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact ha ((Ideal.span_singleton_le_iff_mem _).2 hπ𝔪 ha')
  haveI hQ : ((Ideal.span {π}).map (algebraMap A (Localization.AtPrime 𝔪))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl _ _ hπp hdisj
  -- `π = x u`
  have hπx : algebraMap A (Localization.AtPrime 𝔪) π ∈ Ideal.span {x} := by
    rw [← hloc]; exact Ideal.mem_map_of_mem _ hπ𝔭
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hπx
  have hxQ : x ∈ (Ideal.span {π}).map (algebraMap A (Localization.AtPrime 𝔪)) := by
    have hmem : u * x ∈ (Ideal.span {π}).map (algebraMap A (Localization.AtPrime 𝔪)) := by
      rw [hu]; exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self π)
    rcases hQ.mem_or_mem hmem with h | h
    · exfalso
      rw [Ideal.map_span, Set.image_singleton] at h
      obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h
      have hπ0 : algebraMap A (Localization.AtPrime 𝔪) π ≠ 0 := by
        intro h0
        exact hπ.ne_zero (IsLocalization.injective (Localization.AtPrime 𝔪)
          (Ideal.primeCompl_le_nonZeroDivisors 𝔪) (h0.trans (map_zero _).symm))
      have h3 : algebraMap A (Localization.AtPrime 𝔪) π * (v * x) = u * x := by
        rw [← hv]; ring
      have h1 : algebraMap A (Localization.AtPrime 𝔪) π * (1 - v * x) = 0 := by
        rw [mul_sub, mul_one, h3, hu, sub_self]
      have h2 : 1 - v * x = 0 := (mul_eq_zero.1 h1).resolve_left hπ0
      have hxv : x * v = 1 := by rw [mul_comm]; exact (sub_eq_zero.1 h2).symm
      have : IsUnit x := ⟨⟨x, v, hxv, by rw [mul_comm]; exact hxv⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal x).1 hx this
    · exact h
  apply le_antisymm
  · have h1 : 𝔭.map (algebraMap A (Localization.AtPrime 𝔪)) ≤
        (Ideal.span {π}).map (algebraMap A (Localization.AtPrime 𝔪)) := by
      rw [hloc, Ideal.span_le, Set.singleton_subset_iff]; exact hxQ
    have h2 := Ideal.comap_mono (f := algebraMap A (Localization.AtPrime 𝔪)) h1
    have e1 := IsLocalization.comap_map_of_isPrime_disjoint 𝔪.primeCompl
      (Localization.AtPrime 𝔪) ‹𝔭.IsPrime›
      (by rw [Set.disjoint_left]; intro a ha ha'; exact ha (h𝔭𝔪 ha'))
    have e2 := IsLocalization.comap_map_of_isPrime_disjoint 𝔪.primeCompl
      (Localization.AtPrime 𝔪) hπp hdisj
    exact e1.symm.le.trans (h2.trans e2.le)
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hπ𝔭

end Global

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section Divisorial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} {v₀ : ℕ → ℚ}

/-- In the divisorial case the support of the weights is `{0}`. -/
lemma LocData.supp_zero {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (h0 : v₀ 0 ≠ 0)
    (hk1 : v₀ 1 = 0) (i : Fin D.n) : D.ek i ≠ 0 ↔ (i : ℕ) = 0 := by
  have hv : ∀ j : Fin D.n, D.ek j = v₀ j := fun j => by
    have := congrFun D.hv (j : ℕ); rw [ext0_apply] at this; exact this
  constructor
  · intro hne
    by_contra hi
    have h1 : (1 : ℕ) < D.n := by have := i.2; omega
    have hle : D.ek i ≤ D.ek ⟨1, h1⟩ := D.inv.anti (Fin.le_def.2 (by simp; omega))
    rw [hv ⟨1, h1⟩, hk1] at hle
    exact hne (le_antisymm hle (D.inv.nonneg i))
  · intro hi
    rw [hv i, show (i : ℕ) = 0 from hi]
    exact h0

lemma LocData.n_pos {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (h0 : v₀ 0 ≠ 0) :
    0 < D.n := by
  by_contra h
  apply h0
  have := congrFun D.hv 0
  simp only [ext0, dif_neg h] at this
  exact this.symm

/-- In the divisorial case the component is locally generated by the first coordinate. -/
lemma LocData.P_eq_span {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (h0 : v₀ 0 ≠ 0)
    (hk1 : v₀ 1 = 0) :
    D.P = Ideal.span {(Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x ⟨0, D.n_pos h0⟩} := by
  have hset : {i : Fin D.n | (i : ℕ) < D.k} = {⟨0, D.n_pos h0⟩} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [← D.supp i, D.supp_zero h0 hk1 i, Fin.ext_iff]
  rw [LocData.P, hset, Set.image_singleton]

/-- In the divisorial case the centre ideal `𝓕₁` is a power of the coordinate. -/
lemma RF_le_pow_of_single {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ} (c : Chart S n)
    {e : Fin n → ℚ} (h0 : 0 < n) (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) = 0) {a : ℕ}
    (ha : e ⟨0, h0⟩ = 1 / a) : c.RF e 1 ≤ Ideal.span {c.x ⟨0, h0⟩} ^ a := by
  rw [Chart.RF, Ideal.span_le]
  rintro _ ⟨α, hα0, hα1, rfl⟩
  have hαi : ∀ i : Fin n, i ≠ ⟨0, h0⟩ → α i = 0 := fun i hi => by
    apply hα0 i
    by_contra hne
    exact hi (Fin.ext ((hsupp i).1 hne))
  have hprod : ∏ i, c.x i ^ α i = c.x ⟨0, h0⟩ ^ α ⟨0, h0⟩ := by
    rw [Finset.prod_eq_single ⟨0, h0⟩]
    · intro i _ hi; rw [hαi i hi, pow_zero]
    · simp
  have hlam : lam e α = α ⟨0, h0⟩ * (1 / a) := by
    rw [lam, Finset.sum_eq_single ⟨0, h0⟩, ha]
    · intro i _ hi; rw [hαi i hi]; simp
    · simp
  have ha' : a ≤ α ⟨0, h0⟩ := by
    rw [hlam] at hα1
    rcases Nat.eq_zero_or_pos a with h | h
    · omega
    · have : (a : ℚ) ≤ α ⟨0, h0⟩ := by
        have hapos : (0 : ℚ) < a := by exact_mod_cast h
        rw [mul_one_div, le_div_iff₀ hapos, one_mul] at hα1
        exact hα1
      exact_mod_cast this
  rw [SetLike.mem_coe, hprod, ← Nat.sub_add_cancel ha', pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _)

end Divisorial

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section DivGlobal

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 in
/-- **In the divisorial case the component is principal.** -/
theorem div_eq_span (h0 : v₀ 0 ≠ 0) (hk1 : v₀ 1 = 0) {π : A} (hπ : Prime π) (hπ𝔭 : π ∈ 𝔭) :
    𝔭 = Ideal.span {π} := by
  haveI := h𝔭.1.1
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹_›)
  haveI := h𝔪
  obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 hle
  obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hI𝔪 hv
  have hp : 𝔭 = D.p := D.eq_p_of_minimal h𝔭 hle
  have hloc : 𝔭.map (algebraMap A (Localization.AtPrime 𝔪)) =
      Ideal.span {(Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x ⟨0, D.n_pos h0⟩} := by
    rw [hp, D.map_p, D.P_eq_span h0 hk1]
  exact eq_span_of_loc_principal hle hπ hπ𝔭 (D.cent.x_mem _) hloc

include hI hmax h𝔭 hd hw in
/-- **In the divisorial case `I ⊆ (π^a)`.** -/
theorem div_le_span_pow (h0 : v₀ 0 ≠ 0) (hk1 : v₀ 1 = 0) {π : A} (hπ : Prime π) (hπ𝔭 : π ∈ 𝔭)
    {a : ℕ} (ha : v₀ 0 = 1 / a) : I ≤ Ideal.span {π ^ a} := by
  have h𝔭π := div_eq_span hI hmax h𝔭 h0 hk1 hπ hπ𝔭
  refine (I_le_compFil hI hmax h𝔭 hd).trans ?_
  rw [compFil_F, show ((d : ℤ) : ℚ) / d = 1 by
    have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast; field_simp]
  apply Ideal.le_of_forall_map
  intro 𝔪 _
  by_cases h𝔭𝔪 : 𝔭 ≤ 𝔪
  · rw [compF_map hI hmax h𝔭 𝔪 h𝔭𝔪 1]
    obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
    obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hI𝔪 hv
    rw [D.cRF_eq_transport hI 1]
    have h0' := D.n_pos h0
    have hek : D.ek ⟨0, h0'⟩ = 1 / a := by
      have := congrFun D.hv 0
      rw [ext0, dif_pos h0'] at this
      rw [this, ha]
    refine (RF_le_pow_of_single _ h0' (D.supp_zero h0 hk1) hek).trans ?_
    have hx : Ideal.span {(Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x ⟨0, h0'⟩} =
        (Ideal.span {π}).map (algebraMap A (Localization.AtPrime 𝔪)) := by
      rw [← D.P_eq_span h0 hk1, ← D.map_p, ← D.eq_p_of_minimal h𝔭 h𝔭𝔪, h𝔭π]
    rw [hx, ← Ideal.map_pow, Ideal.span_singleton_pow]
  · have hπ𝔪 : π ∉ 𝔪 := fun h => h𝔭𝔪 (h𝔭π ▸ (Ideal.span_le.2 (Set.singleton_subset_iff.2 h)))
    have hu : IsUnit (algebraMap A (Localization.AtPrime 𝔪) (π ^ a)) :=
      IsLocalization.map_units _ (⟨π ^ a, 𝔪.primeCompl.pow_mem hπ𝔪 a⟩ : 𝔪.primeCompl)
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top.2 hu]
    exact le_top

end DivGlobal

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section DivStep

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- The divisorial weak transform `I : π^a`. -/
def divI (I : Ideal A) (π : A) (a : ℕ) : Ideal A := I.colon {π ^ a}

lemma mem_divI {I : Ideal A} {π : A} {a : ℕ} {f : A} : f ∈ divI I π a ↔ π ^ a * f ∈ I := by
  rw [divI, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]

lemma le_divI (I : Ideal A) (π : A) (a : ℕ) : I ≤ divI I π a :=
  fun f hf => mem_divI.2 (I.mul_mem_left _ hf)

lemma div_eq_mul {I : Ideal A} {π : A} {a : ℕ} (hle : I ≤ Ideal.span {π ^ a}) :
    I = Ideal.span {π ^ a} * divI I π a := by
  apply le_antisymm
  · intro f hf
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 (hle hf)
    have hgI : g ∈ divI I π a := mem_divI.2 (by rw [mul_comm, hg]; exact hf)
    rw [← hg, mul_comm g]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hgI
  · rw [Ideal.mul_le]
    intro x hx y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [mul_assoc]
    exact I.mul_mem_left _ (mem_divI.1 hy)

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {π : A} {a : ℕ} (ha0 : 0 < a) (ha : v₀ 0 = 1 / a) (hle : I ≤ Ideal.span {π ^ a})

include hI hmax ha0 ha hle in
/-- **The divisorial drop**: `V(I : π^a)` misses `V(π)`. -/
theorem div_not_mem (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔪 : divI I π a ≤ 𝔪) : π ∉ 𝔪 := by
  intro hπ𝔪
  have hI𝔪 : I ≤ 𝔪 ^ (a + 1) := by
    rw [div_eq_mul hle, pow_succ]
    refine Ideal.mul_mono ?_ h𝔪
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_pow hπ𝔪 a
  have hI𝔪' : I ≤ 𝔪 := hI𝔪.trans (Ideal.pow_le_self (by omega))
  obtain ⟨v, hv⟩ := exists_invAt hI 𝔪 hI𝔪'
  have h1 := invAt_zero_le_of_le_pow hv (by omega) hI𝔪
  have h2 := hmax 𝔪 hI𝔪' v hv
  have hlt : v 0 < v₀ 0 := by
    rw [ha]
    refine lt_of_le_of_lt h1 ?_
    have : (0 : ℚ) < a := by exact_mod_cast ha0
    push_cast
    exact one_div_lt_one_div_of_lt this (by linarith)
  exact absurd h2 (not_le.2 ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), hlt⟩)

include hI hmax ha0 ha hle in
lemma div_Iloc (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔪 : divI I π a ≤ 𝔪) :
    Iloc I 𝔪 = Iloc (divI I π a) 𝔪 := by
  have := Iloc_span_unit_mul (J := divI I π a) (𝔪 := 𝔪)
    (div_not_mem hI hmax ha0 ha hle 𝔪 h𝔪) a
  rwa [← div_eq_mul hle] at this

include hI hmax ha0 ha hle in
lemma div_invAt_iff (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔪 : divI I π a ≤ 𝔪) {v : ℕ → ℚ} :
    InvAt (divI I π a) 𝔪 v ↔ InvAt I 𝔪 v :=
  ⟨InvAt.of_Iloc_eq (div_Iloc hI hmax ha0 ha hle 𝔪 h𝔪).symm,
    InvAt.of_Iloc_eq (div_Iloc hI hmax ha0 ha hle 𝔪 h𝔪)⟩

include hI hmax ha0 ha hle in
theorem div_inv_ge (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔪 : divI I π a ≤ 𝔪) {v : ℕ → ℚ}
    (hv : InvAt (divI I π a) 𝔪 v) : toLex v₀ ≤ toLex v :=
  hmax 𝔪 ((le_divI I π a).trans h𝔪) v ((div_invAt_iff hI hmax ha0 ha hle 𝔪 h𝔪).1 hv)

lemma divI_ne_bot (hI : I ≠ ⊥) : divI I π a ≠ ⊥ := fun h => hI (eq_bot_iff.2 (h ▸ le_divI I π a))

end DivStep

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section DivCount

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)
  {π : A} (h𝔭π : 𝔭 = Ideal.span {π}) {a : ℕ} (ha0 : 0 < a) (ha : v₀ 0 = 1 / a)
  (hle : I ≤ Ideal.span {π ^ a})

include hI hmax h𝔭 h𝔭π ha0 ha hle in
/-- **The number of components drops** in the divisorial case. -/
theorem div_count :
    (locusIdeal (divI I π a) v₀).minimalPrimes.ncard < (locusIdeal I v₀).minimalPrimes.ncard := by
  classical
  haveI : Algebra.FiniteType ℚ A := inferInstance
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  have hfin : (locusIdeal I v₀).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing A _
  have hπ𝔭 : ∀ Q : Ideal A, π ∉ Q → ¬ 𝔭 ≤ Q := fun Q hπ h =>
    hπ (h (h𝔭π ▸ Ideal.mem_span_singleton_self π))
  have hle' := ncard_minimalPrimes_sInf_le (S := maxLocus (divI I π a) v₀)
    (hfin.toFinset.erase 𝔭) (fun 𝔭' => 𝔭') ?_ ?_ ?_
  · have hcard : (hfin.toFinset.erase 𝔭).card < (locusIdeal I v₀).minimalPrimes.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
      exact Finset.card_erase_lt_of_mem (hfin.mem_toFinset.2 h𝔭)
    exact lt_of_le_of_lt hle' hcard
  · intro 𝔭' h𝔭'
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h𝔭'
    exact h𝔭'.2.1.1
  · intro Q hQ
    obtain ⟨hQm, hIQ, hv⟩ := hQ
    have hπQ := div_not_mem hI hmax ha0 ha hle Q hIQ
    have hv' := (div_invAt_iff hI hmax ha0 ha hle Q hIQ).1 hv
    have hL : locusIdeal I v₀ ≤ Q := sInf_le ⟨hQm, (le_divI I π a).trans hIQ, hv'⟩
    obtain ⟨𝔭', h𝔭', h𝔭'le⟩ := Ideal.exists_minimalPrimes_le hL
    refine ⟨𝔭', ?_, h𝔭'le⟩
    rw [Finset.mem_erase, Set.Finite.mem_toFinset]
    exact ⟨fun h => hπ𝔭 Q hπQ (h ▸ h𝔭'le), h𝔭'⟩
  · intro 𝔭' h𝔭' Q hQ h𝔭'Q
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h𝔭'
    haveI := hQ
    obtain ⟨hIQ, hinv⟩ := mem_maxLocus_of_minimal hI hmax h𝔭'.2 Q h𝔭'Q
    have hπQ : π ∉ Q := fun h => by
      have := minimalPrimes_sup_eq_top hI hmax h𝔭 h𝔭'.2 (Ne.symm h𝔭'.1)
      apply hQ.ne_top
      rw [eq_top_iff, ← this]
      exact sup_le (h𝔭π ▸ Ideal.span_le.2 (Set.singleton_subset_iff.2 h)) h𝔭'Q
    have hdivQ : divI I π a ≤ Q := by
      have h1 := hIQ
      rw [div_eq_mul hle] at h1
      rcases hQ.isPrime.mul_le.1 h1 with h | h
      · exact absurd (hQ.isPrime.mem_of_pow_mem a (h (Ideal.mem_span_singleton_self _))) hπQ
      · exact h
    exact ⟨hQ, hdivQ, (div_invAt_iff hI hmax ha0 ha hle Q hdivQ).2 hinv⟩

end DivCount

section DivDer

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
  {π : A} (h𝔭π : 𝔭 = Ideal.span {π}) {a : ℕ} (ha0 : 0 < a)

include hI hmax h𝔭 hd hw h𝔭π ha0 in
/-- Stabilizing derivations pass to `I : π^a`. -/
theorem deriv_mem_divI (δ : Derivation ℚ A A) (hδ : ∀ f ∈ I, δ f ∈ I) {f : A}
    (hf : f ∈ divI I π a) : δ f ∈ divI I π a := by
  have hπF : π ∈ compF I 𝔭 (1 / d) := by
    rw [compF_one_div hI hmax h𝔭 hd hw, h𝔭π]; exact Ideal.mem_span_singleton_self π
  have hδπ : δ π ∈ Ideal.span {π} := by
    rw [← h𝔭π, ← compF_one_div hI hmax h𝔭 hd hw]
    exact deriv_mem_compF hI hmax h𝔭 δ hδ _ hπF
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hδπ
  rw [mem_divI] at hf ⊢
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h2 : δ (π ^ (b + 1) * f) = π ^ (b + 1) * δ f + ((b + 1 : ℕ) * c) * (π ^ (b + 1) * f) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, ← hc, smul_eq_mul, smul_eq_mul, nsmul_eq_mul,
      smul_eq_mul, Nat.add_sub_cancel]
    push_cast; ring
  have : π ^ (b + 1) * δ f = δ (π ^ (b + 1) * f) - ((b + 1 : ℕ) * c) * (π ^ (b + 1) * f) := by
    rw [h2]; ring
  rw [this]
  exact I.sub_mem (hδ _ hf) (I.mul_mem_left _ hf)

include hI hmax h𝔭 hd hw h𝔭π ha0 in
theorem div_vertOK {m : ℕ} (hV : VertOK I m) : VertOK (divI I π a) m := by
  intro 𝔪 h𝔪 hle
  obtain ⟨δ, y, hδ, hdet⟩ := hV 𝔪 h𝔪 ((le_divI I π a).trans hle)
  exact ⟨δ, y, fun j f hf => deriv_mem_divI hI hmax h𝔭 hd hw h𝔭π ha0 (δ j) (hδ j) hf, hdet⟩

theorem div_dimOK {m N : ℕ} (hD : DimOK I m N) : DimOK (divI I π a) m N :=
  fun 𝔪 _ hle n hc => hD 𝔪 ((le_divI I π a).trans hle) n hc

end DivDer

end BezoutCounterexample.Principalization

