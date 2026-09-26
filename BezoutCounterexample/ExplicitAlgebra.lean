import BezoutCounterexample.Nagata
import BezoutCounterexample.Defs

/-!
# Section 6.3: an explicit first extension — algebra

We study `S = ℚ[u, v, r, s]/(ru + sv - 1)` and `A* = S[t] = ℚ[t,u,v,r,s]/(ru+sv-1)`.

The variables of `P = ℚ[u, s, r, v] = MvPolynomial (Fin 4) ℚ` are ordered so that
`MvPolynomial.finSuccEquiv` identifies `P` with `D[u]`, `D = ℚ[s, r, v]`, and the relation
`f = ru + sv - 1` with the linear polynomial `g = r·u + (sv - 1) ∈ D[u]`.

* `f_prime`: `f` is prime (Gauss's lemma), so `S` is a domain.
* `u_prime`: `u` is a prime element of `S`, since `S/(u) ≅ ℚ[s,r,v]/(sv-1)` is a domain.
* `equivSu`: `S[1/u] ≅ ℚ[u, s, v][1/u]`; hence (Nagata's criterion) `S` is factorial.
* `S` is smooth over `ℚ` (it is covered by `D(u)` and `D(v)`), hence so is `A* = S[t]`.
* `map_span_eq`: `(x - 1, y) A* = t A*`, and `phi_injective`: `ℚ[x,y] → A*` is injective.
-/

noncomputable section

namespace BezoutCounterexample.Explicit

open Polynomial

/-! ### The polynomial rings -/

/-- `P = ℚ[u, s, r, v]` (variables `X 0 = u`, `X 1 = s`, `X 2 = r`, `X 3 = v`). -/
abbrev P : Type := MvPolynomial (Fin 4) ℚ

/-- `D = ℚ[s, r, v]` (variables `X 0 = s`, `X 1 = r`, `X 2 = v`). -/
abbrev D : Type := MvPolynomial (Fin 3) ℚ

/-- The variable `s` of `D`. -/
def sD : D := MvPolynomial.X 0
/-- The variable `r` of `D`. -/
def rD : D := MvPolynomial.X 1
/-- The variable `v` of `D`. -/
def vD : D := MvPolynomial.X 2

/-- `b = s v - 1 ∈ D`. -/
def bD : D := sD * vD - 1

/-- `g = r·u + (s v - 1) ∈ D[u]`. -/
def g : D[X] := C rD * X + C bD

/-- The relation `f = r u + s v - 1 ∈ P`. -/
def f : P := MvPolynomial.X 2 * MvPolynomial.X 0 + MvPolynomial.X 1 * MvPolynomial.X 3 - 1

/-- `P ≃ D[u]`. -/
abbrev eP : P ≃ₐ[ℚ] D[X] := MvPolynomial.finSuccEquiv ℚ 3

lemma eP_f : eP f = g := by
  have h1 : eP (MvPolynomial.X 0) = X := MvPolynomial.finSuccEquiv_X_zero
  have h2 : eP (MvPolynomial.X 1) = C sD := MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have h3 : eP (MvPolynomial.X 2) = C rD := MvPolynomial.finSuccEquiv_X_succ (j := 1)
  have h4 : eP (MvPolynomial.X 3) = C vD := MvPolynomial.finSuccEquiv_X_succ (j := 2)
  simp only [f, map_sub, map_add, map_mul, map_one, h1, h2, h3, h4, g, bD]
  ring

/-! ### `g` and `f` are prime -/

lemma X_one_not_dvd_bD : ¬ (MvPolynomial.X 1 : D) ∣ bD := by
  rintro ⟨c, hc⟩
  have := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) hc
  simp [bD, sD, vD] at this

lemma g_isPrimitive : g.IsPrimitive := by
  intro c hc
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hc
  have h1 : c ∣ rD := by simpa [g] using hc 1
  have h0 : c ∣ bD := by simpa [g] using hc 0
  obtain ⟨k, hk⟩ := h1
  rcases (MvPolynomial.X_prime.irreducible : Irreducible (MvPolynomial.X 1 : D)).isUnit_or_isUnit
    hk with hc' | hk'
  · exact hc'
  · exfalso
    apply X_one_not_dvd_bD
    obtain ⟨m, hm⟩ := h0
    obtain ⟨w, rfl⟩ := hk'
    refine ⟨((w⁻¹ : Dˣ) : D) * m, ?_⟩
    have : c = MvPolynomial.X 1 * ((w⁻¹ : Dˣ) : D) := by
      rw [show (MvPolynomial.X 1 : D) = rD from rfl, hk, mul_assoc, Units.mul_inv, mul_one]
    rw [hm, this]; ring

lemma rD_ne_zero : rD ≠ 0 := MvPolynomial.X_ne_zero 1

theorem g_irreducible : Irreducible g := by
  rw [g_isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := FractionRing D)]
  apply Polynomial.irreducible_of_degree_eq_one
  have hr : algebraMap D (FractionRing D) rD ≠ 0 := by
    intro h
    exact rD_ne_zero ((IsFractionRing.injective D (FractionRing D)) (by rw [h, map_zero]))
  simp only [g, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  exact Polynomial.degree_linear hr

theorem g_prime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.1 g_irreducible

theorem f_prime : Prime f := by
  rw [← MulEquiv.prime_iff eP.toRingEquiv.toMulEquiv]
  show Prime (eP f)
  rw [eP_f]
  exact g_prime

/-! ### The ring `S` -/

/-- `S = ℚ[u, v, r, s]/(ru + sv - 1)`. -/
abbrev S : Type := P ⧸ Ideal.span {f}

instance : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime f_prime.ne_zero).2 f_prime

/-- `S` is a domain. -/
instance : IsDomain S := Ideal.Quotient.isDomain _

/-- The quotient map `P → S`. -/
abbrev mkS : P →ₐ[ℚ] S := Ideal.Quotient.mkₐ ℚ _

/-- The element `u ∈ S`. -/
def u : S := mkS (MvPolynomial.X 0)
/-- The element `s ∈ S`. -/
def s : S := mkS (MvPolynomial.X 1)
/-- The element `r ∈ S`. -/
def r : S := mkS (MvPolynomial.X 2)
/-- The element `v ∈ S`. -/
def v : S := mkS (MvPolynomial.X 3)

lemma mkS_f : mkS f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/-- The defining relation `r u + s v = 1` in `S`. -/
lemma rel : r * u + s * v = 1 := by
  have h := mkS_f
  simp only [f, map_add, map_mul, map_sub, map_one] at h
  simp only [r, u, s, v]
  linear_combination h

/-- Evaluation `S → K` at a point `(u, v, r, s)` with `r u + s v = 1`. -/
def evalS {K : Type*} [CommRing K] [Algebra ℚ K] (pu pv pr ps : K) (h : pr * pu + ps * pv = 1) :
    S →ₐ[ℚ] K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![pu, ps, pr, pv]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have h' : pr * pu + ps * pv - 1 = 0 := by linear_combination h
    simp [f, h'])

@[simp] lemma evalS_u {K : Type*} [CommRing K] [Algebra ℚ K] (pu pv pr ps : K)
    (h : pr * pu + ps * pv = 1) : evalS pu pv pr ps h u = pu := by
  show MvPolynomial.aeval ![pu, ps, pr, pv] (MvPolynomial.X 0) = _
  simp

@[simp] lemma evalS_v {K : Type*} [CommRing K] [Algebra ℚ K] (pu pv pr ps : K)
    (h : pr * pu + ps * pv = 1) : evalS pu pv pr ps h v = pv := by
  show MvPolynomial.aeval ![pu, ps, pr, pv] (MvPolynomial.X 3) = _
  simp

@[simp] lemma evalS_r {K : Type*} [CommRing K] [Algebra ℚ K] (pu pv pr ps : K)
    (h : pr * pu + ps * pv = 1) : evalS pu pv pr ps h r = pr := by
  show MvPolynomial.aeval ![pu, ps, pr, pv] (MvPolynomial.X 2) = _
  simp

@[simp] lemma evalS_s {K : Type*} [CommRing K] [Algebra ℚ K] (pu pv pr ps : K)
    (h : pr * pu + ps * pv = 1) : evalS pu pv pr ps h s = ps := by
  show MvPolynomial.aeval ![pu, ps, pr, pv] (MvPolynomial.X 1) = _
  simp

/-! ### `u` is a prime element of `S` -/

/-- `E = ℚ[r, v]`. -/
abbrev E : Type := MvPolynomial (Fin 2) ℚ

/-- `D ≃ E[s]` (the variable `s` of `D` becomes the polynomial variable). -/
abbrev eD : D ≃ₐ[ℚ] E[X] := MvPolynomial.finSuccEquiv ℚ 2

lemma eD_bD : eD bD = C (MvPolynomial.X 1) * X + C (-1) := by
  have h1 : eD (MvPolynomial.X 0) = X := MvPolynomial.finSuccEquiv_X_zero
  have h3 : eD (MvPolynomial.X 2) = C (MvPolynomial.X 1) := MvPolynomial.finSuccEquiv_X_succ (j := 1)
  simp only [bD, sD, vD, map_sub, map_mul, map_one, h1, h3, map_neg]
  ring

theorem bD_prime : Prime bD := by
  rw [← MulEquiv.prime_iff eD.toRingEquiv.toMulEquiv]
  show Prime (eD bD)
  rw [eD_bD]
  apply UniqueFactorizationMonoid.irreducible_iff_prime.1
  have hprim : (C (MvPolynomial.X 1 : E) * X + C (-1) : E[X]).IsPrimitive := by
    intro c hc
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hc
    have h0 := hc 0
    simp only [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, coeff_C_zero, zero_add] at h0
    exact isUnit_of_dvd_unit h0 (isUnit_one.neg)
  rw [hprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing E)]
  apply Polynomial.irreducible_of_degree_eq_one
  have hr : algebraMap E (FractionRing E) (MvPolynomial.X 1) ≠ 0 := by
    intro h
    exact MvPolynomial.X_ne_zero 1 ((IsFractionRing.injective E (FractionRing E))
      (by rw [h, map_zero]))
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  exact Polynomial.degree_linear hr

/-- `D/(sv - 1)`. -/
abbrev Dq : Type := D ⧸ Ideal.span {bD}

instance : (Ideal.span {bD}).IsPrime := (Ideal.span_singleton_prime bD_prime.ne_zero).2 bD_prime

instance : IsDomain Dq := Ideal.Quotient.isDomain _

/-- The quotient map `D → D/(sv - 1)`. -/
abbrev mkD : D →ₐ[ℚ] Dq := Ideal.Quotient.mkₐ ℚ _

lemma mkD_bD : mkD bD = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

/-- The map `S → D/(sv - 1)`, `u ↦ 0`. -/
def psi : S →ₐ[ℚ] Dq :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![0, mkD sD, mkD rD, mkD vD]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have hb : (Ideal.Quotient.mk (Ideal.span {bD})) (sD * vD - 1) = 0 := mkD_bD
    simp only [map_sub, map_mul, map_one] at hb
    simp [f, hb])

lemma psi_mkS (F : P) : psi (mkS F) = mkD (Polynomial.eval 0 (eP F)) := by
  have : psi.comp mkS =
      mkD.comp (((Polynomial.aeval (0 : D)).restrictScalars ℚ).comp eP.toAlgHom) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 : eP (MvPolynomial.X 0) = X := MvPolynomial.finSuccEquiv_X_zero
    have h2 : eP (MvPolynomial.X 1) = C sD := MvPolynomial.finSuccEquiv_X_succ (j := 0)
    have h3 : eP (MvPolynomial.X 2) = C rD := MvPolynomial.finSuccEquiv_X_succ (j := 1)
    have h4 : eP (MvPolynomial.X 3) = C vD := MvPolynomial.finSuccEquiv_X_succ (j := 2)
    fin_cases i
    · show MvPolynomial.aeval ![0, mkD sD, mkD rD, mkD vD] (MvPolynomial.X 0) =
        mkD (Polynomial.aeval (0 : D) (eP (MvPolynomial.X 0)))
      rw [h1]; simp
    · show MvPolynomial.aeval ![0, mkD sD, mkD rD, mkD vD] (MvPolynomial.X 1) =
        mkD (Polynomial.aeval (0 : D) (eP (MvPolynomial.X 1)))
      rw [h2]; simp
    · show MvPolynomial.aeval ![0, mkD sD, mkD rD, mkD vD] (MvPolynomial.X 2) =
        mkD (Polynomial.aeval (0 : D) (eP (MvPolynomial.X 2)))
      rw [h3]; simp
    · show MvPolynomial.aeval ![0, mkD sD, mkD rD, mkD vD] (MvPolynomial.X 3) =
        mkD (Polynomial.aeval (0 : D) (eP (MvPolynomial.X 3)))
      rw [h4]; simp
  have h := congrArg (fun φ : P →ₐ[ℚ] Dq => φ F) this
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h

lemma ker_psi : RingHom.ker psi = Ideal.span {u} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hz' : psi (mkS F) = 0 := hz
    rw [psi_mkS, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
      ← Polynomial.coeff_zero_eq_eval_zero] at hz'
    obtain ⟨H, hH⟩ := Ideal.mem_span_singleton'.1 hz'
    set G := eP F
    have hG : G = g * C H + X * (G.divX - C rD * C H) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add G]
      rw [← hH, g, map_mul]
      ring
    have hF : F = f * eP.symm (C H) + MvPolynomial.X 0 * eP.symm (G.divX - C rD * C H) := by
      apply eP.injective
      rw [map_add, map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, eP_f,
        MvPolynomial.finSuccEquiv_X_zero]
      exact hG
    show mkS F ∈ Ideal.span {u}
    rw [hF, map_add, map_mul, map_mul, mkS_f, zero_mul, zero_add]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self u)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show psi u = 0
    rw [u, psi_mkS, MvPolynomial.finSuccEquiv_X_zero]
    simp

lemma u_ne_zero : u ≠ 0 := by
  intro h
  have := congrArg (evalS (1 : ℚ) 0 1 0 (by norm_num)) h
  simp at this

/-- `u` is a prime element of `S`. -/
theorem u_prime : Prime u := by
  rw [← Ideal.span_singleton_prime u_ne_zero, ← ker_psi]
  exact RingHom.ker_isPrime psi

/-! ### `S[1/u] ≅ ℚ[u, s, v][1/u]`, hence `S` is factorial -/

/-- `ℚ[u, s, v]` (variables `X 0 = u`, `X 1 = s`, `X 2 = v`). -/
abbrev P3 : Type := MvPolynomial (Fin 3) ℚ

/-- `L = ℚ[u, s, v][1/u]`. -/
abbrev L : Type := Localization.Away (MvPolynomial.X 0 : P3)

/-- `S[1/u]`. -/
abbrev Su : Type := Localization.Away u

/-- `u ∈ L`. -/
def uL : L := algebraMap P3 L (MvPolynomial.X 0)
/-- `s ∈ L`. -/
def sL : L := algebraMap P3 L (MvPolynomial.X 1)
/-- `v ∈ L`. -/
def vL : L := algebraMap P3 L (MvPolynomial.X 2)
/-- `u⁻¹ ∈ L`. -/
def invL : L := IsLocalization.Away.invSelf (MvPolynomial.X 0 : P3)

lemma uL_invL : uL * invL = 1 := IsLocalization.Away.mul_invSelf _

/-- `r = (1 - s v)/u ∈ L`. -/
def rL : L := (1 - sL * vL) * invL

/-- The map `S → L`. -/
def alphaS : S →ₐ[ℚ] L :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![uL, sL, rL, vL]) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have h : rL * uL + sL * vL - 1 = 0 := by
      simp only [rL]; linear_combination (1 - sL * vL) * uL_invL
    simp [f, h])

lemma alphaS_u : alphaS u = uL := by
  show MvPolynomial.aeval ![uL, sL, rL, vL] (MvPolynomial.X 0) = _; simp
lemma alphaS_s : alphaS s = sL := by
  show MvPolynomial.aeval ![uL, sL, rL, vL] (MvPolynomial.X 1) = _; simp
lemma alphaS_r : alphaS r = rL := by
  show MvPolynomial.aeval ![uL, sL, rL, vL] (MvPolynomial.X 2) = _; simp
lemma alphaS_v : alphaS v = vL := by
  show MvPolynomial.aeval ![uL, sL, rL, vL] (MvPolynomial.X 3) = _; simp

lemma isUnit_uL : IsUnit uL := IsLocalization.Away.algebraMap_isUnit _

/-- The map `S[1/u] → L`. -/
def alpha : Su →ₐ[ℚ] L :=
  IsLocalization.Away.liftAlgHom u (f := alphaS) (by rw [alphaS_u]; exact isUnit_uL)

lemma alpha_algebraMap (z : S) : alpha (algebraMap S Su z) = alphaS z := by
  simp [alpha, IsLocalization.Away.liftAlgHom]

/-- The map `ℚ[u, s, v] → S[1/u]`. -/
def beta0 : P3 →ₐ[ℚ] Su :=
  MvPolynomial.aeval ![algebraMap S Su u, algebraMap S Su s, algebraMap S Su v]

lemma isUnit_u' : IsUnit (algebraMap S Su u) := IsLocalization.Away.algebraMap_isUnit _

/-- The map `L → S[1/u]`. -/
def beta : L →ₐ[ℚ] Su :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X 0 : P3) (f := beta0) (by
    simp only [beta0, MvPolynomial.aeval_X, Matrix.cons_val_zero]; exact isUnit_u')

lemma beta_algebraMap (z : P3) : beta (algebraMap P3 L z) = beta0 z := by
  simp [beta, IsLocalization.Away.liftAlgHom]

lemma beta_uL : beta uL = algebraMap S Su u := by
  rw [uL, beta_algebraMap]; simp [beta0]
lemma beta_sL : beta sL = algebraMap S Su s := by
  rw [sL, beta_algebraMap]; simp [beta0]
lemma beta_vL : beta vL = algebraMap S Su v := by
  rw [vL, beta_algebraMap]; simp [beta0]

lemma beta_rL : beta rL = algebraMap S Su r := by
  have h1 : algebraMap S Su u * beta invL = 1 := by
    rw [← beta_uL, ← map_mul, uL_invL, map_one]
  have h2 : algebraMap S Su r * algebraMap S Su u + algebraMap S Su s * algebraMap S Su v = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, rel, map_one]
  simp only [rL, map_mul, map_sub, map_one, beta_sL, beta_vL]
  linear_combination (algebraMap S Su r) * h1 - beta invL * h2

lemma alpha_beta : alpha.comp beta = AlgHom.id ℚ L := by
  apply IsLocalization.algHom_ext (Submonoid.powers (MvPolynomial.X 0 : P3))
  apply MvPolynomial.algHom_ext
  intro i
  change alpha (beta (algebraMap P3 L (MvPolynomial.X i))) = algebraMap P3 L (MvPolynomial.X i)
  rw [beta_algebraMap]
  fin_cases i
  · simp [beta0, alpha_algebraMap, alphaS_u, uL]
  · simp [beta0, alpha_algebraMap, alphaS_s, sL]
  · simp [beta0, alpha_algebraMap, alphaS_v, vL]

lemma beta_alpha : beta.comp alpha = AlgHom.id ℚ Su := by
  apply IsLocalization.algHom_ext (Submonoid.powers u)
  apply Ideal.Quotient.algHom_ext ℚ
  apply MvPolynomial.algHom_ext
  intro i
  change beta (alpha (algebraMap S Su (mkS (MvPolynomial.X i)))) = algebraMap S Su (mkS (MvPolynomial.X i))
  rw [alpha_algebraMap]
  fin_cases i
  · exact (congrArg beta alphaS_u).trans beta_uL
  · exact (congrArg beta alphaS_s).trans beta_sL
  · exact (congrArg beta alphaS_r).trans beta_rL
  · exact (congrArg beta alphaS_v).trans beta_vL

/-- `S[1/u] ≃ ℚ[u, s, v][1/u]`. -/
def equivSu : Su ≃ₐ[ℚ] L := AlgEquiv.ofAlgHom alpha beta alpha_beta beta_alpha

instance : UniqueFactorizationMonoid L :=
  UniqueFactorizationMonoid.of_isLocalization (Submonoid.powers (MvPolynomial.X 0 : P3))
    (by rintro ⟨n, hn⟩; exact pow_ne_zero n (MvPolynomial.X_ne_zero 0) hn) L

instance : UniqueFactorizationMonoid Su :=
  MulEquiv.uniqueFactorizationMonoid equivSu.symm.toMulEquiv inferInstance

/-- **`S` is factorial** (Nagata's criterion applied to the prime element `u`). -/
instance : UniqueFactorizationMonoid S :=
  UniqueFactorizationMonoid.of_isLocalization_away u_prime Su

/-! ### Smoothness of `S` -/

instance : Algebra.FinitePresentation ℚ S :=
  Algebra.FinitePresentation.quotient ⟨{f}, by simp⟩

instance : Algebra.FormallySmooth P3 L :=
  Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (MvPolynomial.X 0 : P3))

instance : Algebra.FinitePresentation P3 L :=
  IsLocalization.Away.finitePresentation (S := L) (MvPolynomial.X 0 : P3)

instance : Algebra.Smooth P3 L := ⟨inferInstance, inferInstance⟩

instance : Algebra.Smooth ℚ L := Algebra.Smooth.comp ℚ P3 L

instance : Algebra.Smooth ℚ Su := Algebra.Smooth.of_equiv equivSu.symm

/-- The automorphism of `P` exchanging `u ↔ v` and `s ↔ r`. -/
def swapP : P →ₐ[ℚ] P :=
  MvPolynomial.aeval ![MvPolynomial.X 3, MvPolynomial.X 2, MvPolynomial.X 1, MvPolynomial.X 0]

lemma swapP_f : swapP f = f := by
  simp [swapP, f]; ring

/-- The induced endomorphism of `S`. -/
def swapS : S →ₐ[ℚ] S :=
  Ideal.Quotient.liftₐ _ (mkS.comp swapP) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [AlgHom.comp_apply, map_mul, map_mul, swapP_f, mkS_f, mul_zero])

lemma swapS_mkS (F : P) : swapS (mkS F) = mkS (swapP F) := rfl

lemma swapS_swapS : swapS.comp swapS = AlgHom.id ℚ S := by
  apply Ideal.Quotient.algHom_ext ℚ
  apply MvPolynomial.algHom_ext
  intro i
  change swapS (swapS (mkS (MvPolynomial.X i))) = mkS (MvPolynomial.X i)
  rw [swapS_mkS, swapS_mkS]
  fin_cases i <;> simp [swapP]

/-- The involution of `S` exchanging `u ↔ v`, `s ↔ r`. -/
def swapEquiv : S ≃ₐ[ℚ] S := AlgEquiv.ofAlgHom swapS swapS swapS_swapS swapS_swapS

lemma swapEquiv_u : swapEquiv u = v := by
  show swapS (mkS (MvPolynomial.X 0)) = mkS (MvPolynomial.X 3)
  rw [swapS_mkS]; simp [swapP]

/-- `S[1/v]`. -/
abbrev Sv : Type := Localization.Away v

lemma map_powers_u :
    Submonoid.map swapEquiv.toRingEquiv.toMonoidHom (Submonoid.powers u) = Submonoid.powers v := by
  rw [Submonoid.map_powers]
  have : swapEquiv.toRingEquiv.toMonoidHom u = v := swapEquiv_u
  rw [this]

/-- `S[1/u] ≃ S[1/v]` via the involution. -/
def equivSuSv : Su ≃+* Sv :=
  IsLocalization.ringEquivOfRingEquiv Su Sv swapEquiv.toRingEquiv map_powers_u

instance : Algebra.Smooth ℚ Sv := Algebra.Smooth.of_equiv equivSuSv.toRatAlgEquiv

/-- **`S` is smooth over `ℚ`**: it is covered by `D(u)` and `D(v)` (as `r u + s v = 1`), and
both `S[1/u] ≅ ℚ[u, s, v][1/u]` and `S[1/v] ≅ S[1/u]` are smooth. -/
instance : Algebra.Smooth ℚ S := by
  have hu : ↑(PrimeSpectrum.basicOpen u) ⊆ Algebra.smoothLocus ℚ S :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.2 inferInstance
  have hv : ↑(PrimeSpectrum.basicOpen v) ⊆ Algebra.smoothLocus ℚ S :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.2 inferInstance
  have huniv : Algebra.smoothLocus ℚ S = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true]
    by_cases hup : u ∈ p.asIdeal
    · have hvp : v ∉ p.asIdeal := by
        intro hvp
        apply p.isPrime.ne_top
        rw [Ideal.eq_top_iff_one, ← rel]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hup) (Ideal.mul_mem_left _ _ hvp)
      exact hv (PrimeSpectrum.mem_basicOpen _ _ |>.2 hvp)
    · exact hu (PrimeSpectrum.mem_basicOpen _ _ |>.2 hup)
  exact ⟨Algebra.smoothLocus_eq_univ_iff.1 huniv, inferInstance⟩

/-! ### The ring `A* = S[t]` -/

/-- `A* = ℚ[t, u, v, r, s]/(ru + sv - 1) = S[t]` (the polynomial ring in one variable `t`
over `S`). -/
abbrev Astar : Type := MvPolynomial (Fin 1) S

/-- The variable `t`. -/
def t : Astar := MvPolynomial.X 0

/-- Constants `S → A*`. -/
abbrev CS : S →+* Astar := MvPolynomial.C

/-- `A*` is smooth over `ℚ`. -/
instance : Algebra.Smooth ℚ Astar := Algebra.Smooth.comp ℚ S Astar

/-- `A*` as a smooth finitely generated factorial `ℚ`-domain. -/
def AstarSFD : SmoothFactorialDomain := ⟨Astar⟩

/-- The homomorphism `ℚ[x,y] → A*`, `x ↦ 1 + t u`, `y ↦ t v`. -/
def phi : A₀ →ₐ[ℚ] Astar := MvPolynomial.aeval ![1 + t * CS u, t * CS v]

@[simp] lemma phi_x : phi x = 1 + t * CS u := by simp [phi, x]
@[simp] lemma phi_y : phi y = t * CS v := by simp [phi, y]

/-- `(u, v) = A*`. -/
lemma span_u_v : (Ideal.span {CS u, CS v} : Ideal Astar) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have : CS r * CS u + CS s * CS v = (1 : Astar) := by
    rw [← map_mul, ← map_mul, ← map_add, rel, map_one]
  rw [← this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- **`(x - 1, y) A* = t A*`**; in particular `(x - 1, y)` becomes principal in `A*`. -/
theorem map_span_eq : (Ideal.span {x - 1, y} : Ideal A₀).map phi = Ideal.span {t} := by
  rw [Ideal.map_span, Set.image_pair, map_sub, map_one, phi_x, phi_y,
    show (1 + t * CS u - 1 : Astar) = t * CS u by ring]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have : t = CS r * (t * CS u) + CS s * (t * CS v) := by
      have h := congrArg CS rel
      rw [map_add, map_mul, map_mul, map_one] at h
      linear_combination (-t) * h
    have hmem : CS r * (t * CS u) + CS s * (t * CS v) ∈
        (Ideal.span {t * CS u, t * CS v} : Ideal Astar) :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    rw [← this] at hmem
    exact hmem

/-- **`ℚ[x,y] → A*` is injective**: composing with `A* → ℚ(x,y)`, `t ↦ 1`, `u ↦ x - 1`, `v ↦ y`,
`r ↦ (x-1)⁻¹`, `s ↦ 0` gives the inclusion `ℚ[x,y] ⊂ ℚ(x,y)`. -/
theorem phi_injective : Function.Injective phi := by
  set K := Localization.Away (x - 1 : A₀)
  have hx1 : (x - 1 : A₀) ≠ 0 := by
    intro h'
    have := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) h'
    simp [x] at this
  have hinj : Function.Injective (algebraMap A₀ K) :=
    IsLocalization.injective (M := Submonoid.powers (x - 1 : A₀)) K (by
      rintro _ ⟨n, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hx1))
  let ev : S →ₐ[ℚ] K := evalS (algebraMap A₀ K (x - 1)) (algebraMap A₀ K y)
    (IsLocalization.Away.invSelf (x - 1 : A₀)) 0
    (by rw [mul_comm, IsLocalization.Away.mul_invSelf]; ring)
  let ψ : Astar →+* K := MvPolynomial.eval₂Hom ev.toRingHom (fun _ => 1)
  have hcomp : ψ.comp (phi : A₀ →+* Astar) = algebraMap A₀ K := by
    apply MvPolynomial.ringHom_ext
    · intro q
      have h1 : (MvPolynomial.C q : A₀) = algebraMap ℚ A₀ q := rfl
      rw [RingHom.comp_apply, h1, AlgHom.coe_toRingHom, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply,
        show algebraMap ℚ Astar q = MvPolynomial.C (algebraMap ℚ S q) from rfl]
      simp only [ψ, MvPolynomial.eval₂Hom_C]
      exact ev.commutes q
    · intro i
      fin_cases i
      · change ψ (phi x) = algebraMap A₀ K x
        rw [phi_x]
        simp [ψ, ev, t, map_sub]
      · change ψ (phi y) = algebraMap A₀ K y
        rw [phi_y]
        simp [ψ, ev, t]
  have e : ∀ z, ψ (phi z) = algebraMap A₀ K z := fun z => congrArg (fun g => g z) hcomp
  intro a b hab
  apply hinj
  have h := congrArg ψ hab
  rw [e, e] at h
  exact h

end BezoutCounterexample.Explicit
