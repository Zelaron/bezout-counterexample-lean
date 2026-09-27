import BezoutCounterexample.Principalization.MaxLocus

/-!
# The global weighted extended Rees algebra of a component

Notation 3.4 and Lemma 3.5 (2), (4) (`lem:rees`) of the paper.

* `WFil.loc`, `reesMap_isLocalization`: extended Rees algebras localize.
* `compFil`: the filtration `F_j = 𝓕_{j/d}` of a component of the maximal locus.
* `compFil_le_iSup`, `reesAlg_eq_adjoin`, `reesAlg_finiteType`: generation in degrees `≤ d`.
* `reesLoc_formallySmooth`, `rees_smooth`: the extended Rees algebra is smooth over `ℚ`.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section ReesLoc

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (L : Type*) [CommRing L] [Algebra ℚ L]
  [Algebra B L]

/-- The extended filtration. -/
def WFil.loc : WFil L where
  F j := (Φ.F j).map (algebraMap B L)
  mul_le a b := by rw [← Ideal.map_mul]; exact Ideal.map_mono (Φ.mul_le a b)
  zero_eq := by rw [Φ.zero_eq, Ideal.map_top]

/-- The coefficientwise map of Laurent polynomials. -/
abbrev lmap {L : Type*} [CommRing L] (f : B →+* L) : B[T;T⁻¹] →+* L[T;T⁻¹] := AddMonoidAlgebra.mapRingHom ℤ f

omit [Algebra ℚ B] in
lemma lmap_coeff {L : Type*} [CommRing L] (f : B →+* L) (p : B[T;T⁻¹]) (j : ℤ) : (lmap f p).coeff j = f (p.coeff j) :=
  AddMonoidAlgebra.coeff_mapRingHom f p j

omit [Algebra ℚ B] in
lemma lmap_C_mul_T {L : Type*} [CommRing L] [Algebra ℚ L] (f : B →+* L) (b : B) (j : ℤ) :
    lmap f (LaurentPolynomial.C b * T j) = LaurentPolynomial.C (f b) * T j := by
  ext m
  rw [lmap_coeff, coeff_C_mul_T, coeff_C_mul_T]
  split_ifs <;> simp

lemma laurent_coeff_sum {L : Type*} [CommRing L] {ι : Type*} (s : Finset ι) (f : ι → L[T;T⁻¹]) (j : ℤ) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.sum_insert his, Finset.sum_insert his, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih]

/-- The induced map of extended Rees algebras. -/
def reesMap : ReesAlg Φ →+* ReesAlg (Φ.loc L) :=
  ((lmap (algebraMap B L)).comp (ReesAlg Φ).val.toRingHom).codRestrict
    (ReesAlg (Φ.loc L)).toSubring (fun p j => by
      show (lmap (algebraMap B L) p).coeff j ∈ (Φ.F j).map (algebraMap B L)
      rw [lmap_coeff]
      exact Ideal.mem_map_of_mem _ (p.2 j))

omit [Algebra ℚ L] [Algebra ℚ B] in
lemma reesMap_coe (p : ReesAlg Φ) :
    (reesMap Φ L p : L[T;T⁻¹]) = lmap (algebraMap B L) p := rfl

variable [IsDomain B] (M : Submonoid B) [IsLocalization M L]

omit [IsDomain B] [Algebra ℚ L] [Algebra ℚ B] in
/-- **The extended Rees algebra localizes**: `(Φ-Rees) ⊗ M⁻¹B` is the Rees algebra of the
localized filtration. -/
theorem reesMap_isLocalization (hM : M ≤ nonZeroDivisors B) :
    @IsLocalization _ _ (M.map (algebraMap B (ReesAlg Φ))) (ReesAlg (Φ.loc L)) _
      (reesMap Φ L).toAlgebra := by
  classical
  let : Algebra (ReesAlg Φ) (ReesAlg (Φ.loc L)) := (reesMap Φ L).toAlgebra
  have hinjB : Function.Injective (algebraMap B L) := IsLocalization.injective L hM
  have hmapB : ∀ b : B, algebraMap (ReesAlg Φ) (ReesAlg (Φ.loc L))
      (algebraMap B (ReesAlg Φ) b) = algebraMap L _ (algebraMap B L b) := by
    intro b
    apply Subtype.ext
    show lmap (algebraMap B L) (algebraMap B B[T;T⁻¹] b) = algebraMap L L[T;T⁻¹] (algebraMap B L b)
    rw [← LaurentPolynomial.C_eq_algebraMap, ← LaurentPolynomial.C_eq_algebraMap]
    ext m
    rw [lmap_coeff, LaurentPolynomial.C_apply, LaurentPolynomial.C_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩⟩
    rw [hmapB]
    exact (IsLocalization.map_units L ⟨m, hm⟩).map _
  · intro z
    -- clear denominators coefficientwise
    have hco : ∀ j, ∃ (a : B) (m : M), a ∈ Φ.F j ∧
        (z : L[T;T⁻¹]).coeff j * algebraMap B L m = algebraMap B L a := by
      intro j
      obtain ⟨⟨a, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M L).1 (z.2 j)
      exact ⟨a, m, a.2, hm⟩
    choose a m ha hm using hco
    set S := (z : L[T;T⁻¹]).coeff.support
    set μ : M := ∏ j ∈ S, m j
    set q : B[T;T⁻¹] := ∑ j ∈ S,
      LaurentPolynomial.C (a j * ∏ j' ∈ S.erase j, (m j' : B)) * T j
    have hq : q ∈ ReesAlg Φ := by
      refine Subalgebra.sum_mem _ fun j _ => C_mul_T_mem_ReesAlg ?_
      exact Ideal.mul_mem_right _ _ (ha j)
    refine ⟨⟨⟨q, hq⟩, ⟨algebraMap B (ReesAlg Φ) μ, ⟨μ, μ.2, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    simp only
    rw [hmapB]
    show (z : L[T;T⁻¹]) * algebraMap L L[T;T⁻¹] (algebraMap B L μ) = lmap (algebraMap B L) q
    ext j
    rw [← LaurentPolynomial.C_eq_algebraMap, mul_comm, coeff_C_mul', lmap_coeff]
    have hqj : q.coeff j = if j ∈ S then a j * ∏ j' ∈ S.erase j, (m j' : B) else 0 := by
      simp only [q]
      rw [laurent_coeff_sum]
      simp_rw [coeff_C_mul_T]
      rw [Finset.sum_ite_eq]
    rw [hqj]
    split_ifs with hj
    · rw [map_mul, ← hm j, map_prod, mul_comm, mul_assoc]
      congr 1
      rw [Submonoid.coe_finsetProd, map_prod, ← Finset.mul_prod_erase S _ hj]
    · have : (z : L[T;T⁻¹]).coeff j = 0 := Finsupp.notMem_support_iff.1 hj
      rw [this, mul_zero, map_zero]
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (reesMap Φ L x : L[T;T⁻¹]) = reesMap Φ L y := congrArg Subtype.val hxy
    rw [reesMap_coe, reesMap_coe] at this
    have hxy' : (x : B[T;T⁻¹]) = y := by
      ext j
      have := congrArg (fun p : L[T;T⁻¹] => p.coeff j) this
      simp only [lmap_coeff] at this
      exact hinjB this
    simp [Subtype.ext hxy']

end ReesLoc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- Local–global principle for ideals of a domain. -/
lemma Ideal.le_of_forall_map {J J' : Ideal A}
    (h : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], J.map (algebraMap A (Localization.AtPrime 𝔪)) ≤
      J'.map (algebraMap A (Localization.AtPrime 𝔪))) : J ≤ J' := by
  intro x hx
  by_contra hx'
  have hcol : J'.colon (Ideal.span {x}) ≠ ⊤ := by
    intro htop
    apply hx'
    have : (1 : A) ∈ J'.colon (Ideal.span {x}) := by rw [htop]; trivial
    have := Submodule.mem_colon.1 this x (Ideal.mem_span_singleton_self x)
    simpa using this
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hcol
  have := h𝔪
  have h1 := h 𝔪 (Ideal.mem_map_of_mem _ hx)
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪.primeCompl] at h1
  obtain ⟨m, hm, hmx⟩ := h1
  apply hm
  apply hle
  rw [Submodule.mem_colon]
  intro y hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [smul_eq_mul, show m * (z * x) = z * (m * x) by ring]
  exact J'.mul_mem_left _ hmx

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) (d : ℕ)

/-- The component filtration `F_j = 𝓕_{j/d}` as a filtration. -/
def compFil : WFil A where
  F j := compF I 𝔭 ((j : ℚ) / d)
  mul_le a b := by
    rw [Ideal.mul_le]
    intro f hf g hg
    rw [mem_compF] at hf hg ⊢
    intro 𝔪 _ h𝔭𝔪
    have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
    have := cRF_mul_le hI hZ.1 hZ.2 _ _ (Ideal.mul_mem_mul (hf 𝔪 h𝔭𝔪) (hg 𝔪 h𝔭𝔪))
    rw [map_mul]
    convert this using 2
    push_cast; ring
  zero_eq := by
    ext f
    simp only [Int.cast_zero, zero_div, Submodule.mem_top, iff_true]
    rw [mem_compF]
    intro 𝔪 _ h𝔭𝔪
    have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
    rw [cRF_of_nonpos hI hZ.1 hZ.2 le_rfl]; trivial

include hI hmax h𝔭

lemma compFil_F (j : ℤ) : (compFil hI hmax h𝔭 d).F j = compF I 𝔭 ((j : ℚ) / d) := rfl

lemma compFil_loc_F (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : 𝔭 ≤ 𝔪) (j : ℤ) :
    ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)).F j = cRF I 𝔪 ((j : ℚ) / d) :=
  compF_map hI hmax h𝔭 𝔪 h𝔭𝔪 _

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- The weights of an invariant are at most one. -/
lemma IsInv.le_one {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {I : Ideal S} {n : ℕ}
    {e : Fin n → ℚ} (he : IsInv I n e) (hIm : I ≤ maximalIdeal S) (i : Fin n) : e i ≤ 1 := by
  obtain ⟨⟨J, -, rfl⟩, hmin⟩ := he
  set J₁ : MC S n := ⟨J.c, fun _ => 1, J.centred, fun _ => zero_le_one, fun _ _ _ => le_rfl⟩
  have hadm : J₁.Adm I := by
    refine hIm.trans ?_
    show maximalIdeal S ≤ J.c.RF (fun _ => 1) 1
    rw [J.centred, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact J.c.x_mem_RF (fun _ => 1) i one_ne_zero
  have h1 := hmin J₁ hadm
  have h0 : J.e ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.2⟩ ≤ 1 := by
    by_contra hlt
    push Not at hlt
    refine absurd h1 (not_le.2 ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) i.2⟩, fun j hj => ?_, hlt⟩)
    exact absurd hj (Nat.not_lt_zero _)
  exact (J.anti (Fin.le_def.2 (Nat.zero_le _))).trans h0

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- **Generation in bounded degrees**: `F_j = ∑_{1 ≤ l ≤ d} F_l F_{j-l}` for `j > d`. -/
theorem compFil_le_iSup {j : ℤ} (hj : (d : ℤ) < j) :
    (compFil hI hmax h𝔭 d).F j ≤
      ⨆ l ∈ Finset.Icc (1 : ℤ) d, (compFil hI hmax h𝔭 d).F l * (compFil hI hmax h𝔭 d).F (j - l) := by
  set Φ := compFil hI hmax h𝔭 d
  apply Ideal.le_of_forall_map
  intro 𝔪 _
  by_cases h𝔭𝔪 : 𝔭 ≤ 𝔪
  · have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
    obtain ⟨n, e, ⟨⟨J, hJ, hJe⟩, hmin⟩, hev⟩ := hZ.2
    have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
    have hloc : ∀ l : ℤ, (Φ.F l).map (algebraMap A (Localization.AtPrime 𝔪)) =
        J.RF ((l : ℚ) / d) := fun l => by
      rw [show (Φ.F l).map _ = (Φ.loc (Localization.AtPrime 𝔪)).F l from rfl,
        compFil_loc_F hI hmax h𝔭 d 𝔪 h𝔭𝔪, cRF_eq hI hZ.1 hJ hJi]
    rw [hloc, MC.RF, Chart.RF, Ideal.span_le]
    rintro _ ⟨α, h0, hα, rfl⟩
    -- pick a coordinate occurring in `α`
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [lam_zero] at hα
      have : (0 : ℚ) < (j : ℚ) / d := div_pos (by exact_mod_cast (by omega : (0 : ℤ) < j))
        (by exact_mod_cast hd)
      linarith
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h; push Not at h; exact hα0 (Finsupp.ext h)
    have hei : J.e i ≠ 0 := fun h => hi (h0 i h)
    have hv : J.e i = v₀ i := by
      rw [← hev, hJe, ext0_apply]
    obtain ⟨w, hw'⟩ := hw i
    rw [← hv] at hw'
    have hle1 : J.e i ≤ 1 := hJi.le_one (Iloc_le hZ.1) i
    have hpos : 0 < J.e i := lt_of_le_of_ne (J.nonneg i) (Ne.symm hei)
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hw1 : 1 ≤ w := by
      have : (0 : ℚ) < w := by rw [hw']; positivity
      exact_mod_cast this
    have hwd : w ≤ d := by
      have : (w : ℚ) ≤ d := by rw [hw']; nlinarith
      exact_mod_cast this
    have hei' : J.e i = (w : ℚ) / d := by rw [hw']; field_simp
    -- split off `x_i`
    set β := α - Finsupp.single i 1
    have hαβ : α = β + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have hprod : ∏ l, J.c.x l ^ α l = J.c.x i * ∏ l, J.c.x l ^ β l := by
      rw [hαβ]
      simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [mul_comm, Finset.prod_eq_single i]
      · simp
      · intro l _ hl; simp [Ne.symm hl]
      · simp
    have hlamβ : lam J.e β = lam J.e α - J.e i := by
      rw [hαβ, lam_add, lam_single]; ring
    have h1 : J.c.x i ∈ J.RF ((w : ℤ) / (d : ℚ)) := by
      have := J.c.x_mem_RF J.e i hei
      rw [hei'] at this; push_cast; exact this
    have h2 : ∏ l, J.c.x l ^ β l ∈ J.RF (((j - w : ℤ) : ℚ) / d) := by
      apply Ideal.subset_span
      refine ⟨β, fun l hl => ?_, ?_, rfl⟩
      · have := h0 l hl
        rw [hαβ, Finsupp.add_apply] at this
        omega
      · rw [hlamβ, hei']
        push_cast
        rw [sub_div]
        linarith
    rw [SetLike.mem_coe, hprod, Ideal.map_iSup]
    refine Ideal.mem_iSup_of_mem (w : ℤ) ?_
    rw [Ideal.map_iSup]
    refine Ideal.mem_iSup_of_mem (Finset.mem_Icc.2 ⟨by exact_mod_cast hw1, by exact_mod_cast hwd⟩) ?_
    rw [Ideal.map_mul, hloc, hloc]
    exact Ideal.mul_mem_mul h1 h2
  · have htop : ∀ l : ℤ, (Φ.F l).map (algebraMap A (Localization.AtPrime 𝔪)) = ⊤ := fun l =>
      compF_map_of_not_le hI hmax h𝔭 hd hw 𝔪 h𝔭𝔪 _
    rw [htop]
    refine le_top.trans (le_of_eq ?_)
    symm
    rw [Ideal.map_iSup, eq_top_iff]
    refine le_trans ?_ (le_iSup _ (1 : ℤ))
    rw [Ideal.map_iSup]
    refine le_trans ?_ (le_iSup _ (Finset.mem_Icc.2 ⟨le_rfl, by exact_mod_cast hd⟩))
    rw [Ideal.map_mul, htop, htop, Ideal.top_mul]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) (d : ℕ)

include hI hmax h𝔭 in
lemma compFil_F_nonpos {j : ℤ} (hj : j ≤ 0) : (compFil hI hmax h𝔭 d).F j = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [compFil_F, mem_compF]
  intro 𝔪 _ h𝔭𝔪
  have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  rw [cRF_of_nonpos hI hZ.1 hZ.2 (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hj)
    (Nat.cast_nonneg d))]
  trivial

/-- Finite generating sets of the filtration steps. -/
def gensF (j : ℤ) : Finset A :=
  (IsNoetherian.noetherian ((compFil hI hmax h𝔭 d).F j : Submodule A A)).choose

lemma span_gensF (j : ℤ) : Ideal.span (gensF hI hmax h𝔭 d j : Set A) = (compFil hI hmax h𝔭 d).F j :=
  (IsNoetherian.noetherian ((compFil hI hmax h𝔭 d).F j : Submodule A A)).choose_spec

/-- Generators of the extended Rees algebra: `T⁻¹` and `g T^j` for generators `g` of `F_j`,
`1 ≤ j ≤ d`. -/
def reesGenSet : Set A[T;T⁻¹] :=
  {T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) d,
    (fun g => LaurentPolynomial.C g * T j) '' (gensF hI hmax h𝔭 d j : Set A)

lemma reesGenSet_finite : (reesGenSet hI hmax h𝔭 d).Finite := by
  refine (Set.finite_singleton _).union ?_
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => ?_
  exact (Finset.finite_toSet _).image _

lemma reesGenSet_subset : reesGenSet hI hmax h𝔭 d ⊆ ReesAlg (compFil hI hmax h𝔭 d) := by
  rintro _ (h | h)
  · rw [Set.mem_singleton_iff] at h
    subst h
    have : (T (-1) : A[T;T⁻¹]) = LaurentPolynomial.C 1 * T (-1) := by simp
    rw [this]
    exact C_mul_T_mem_ReesAlg (by rw [compFil_F_nonpos hI hmax h𝔭 d (by norm_num)]; trivial)
  · simp only [Set.mem_iUnion, Set.mem_image] at h
    obtain ⟨j, -, g, hg, rfl⟩ := h
    exact C_mul_T_mem_ReesAlg (by rw [← span_gensF]; exact Ideal.subset_span hg)

variable (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hd hw

/-- Every homogeneous element lies in the algebra generated by `reesGenSet`. -/
theorem C_mul_T_mem_adjoin (j : ℤ) (f : A) (hf : f ∈ (compFil hI hmax h𝔭 d).F j) :
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (reesGenSet hI hmax h𝔭 d) := by
  set R' := Algebra.adjoin A (reesGenSet hI hmax h𝔭 d)
  set Φ := compFil hI hmax h𝔭 d
  -- the ideal of coefficients in degree `j`
  let Mj : ℤ → Ideal A := fun j =>
    (Subalgebra.toSubmodule R').comap ((LinearMap.lsmul A A[T;T⁻¹]).flip (T j))
  have hMj : ∀ j f, f ∈ Mj j ↔ LaurentPolynomial.C f * T j ∈ R' := fun j f => by
    show f • (T j : A[T;T⁻¹]) ∈ R' ↔ _
    rw [Algebra.smul_def, ← LaurentPolynomial.C_eq_algebraMap]
  have base : ∀ j : ℤ, j ≤ d → ∀ f ∈ Φ.F j, LaurentPolynomial.C f * T j ∈ R' := by
    intro j hjd f hf
    by_cases hj0 : j ≤ 0
    · have h1 : (LaurentPolynomial.C f * T j : A[T;T⁻¹]) =
          algebraMap A A[T;T⁻¹] f * (T (-1)) ^ (-j).toNat := by
        rw [← LaurentPolynomial.C_eq_algebraMap, T_pow]
        congr 2
        omega
      rw [h1]
      exact R'.mul_mem (R'.algebraMap_mem f)
        (R'.pow_mem (Algebra.subset_adjoin (Or.inl rfl)) _)
    · have hj1 : 1 ≤ j := by omega
      rw [← hMj]
      have hle : Φ.F j ≤ Mj j := by
        rw [← span_gensF, Ideal.span_le]
        intro g hg
        rw [SetLike.mem_coe, hMj]
        apply Algebra.subset_adjoin
        right
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨j, Finset.mem_Icc.2 ⟨hj1, hjd⟩, g, hg, rfl⟩
      exact hle hf
  have main : ∀ N : ℕ, ∀ j : ℤ, j ≤ N → ∀ f ∈ Φ.F j, LaurentPolynomial.C f * T j ∈ R' := by
    intro N
    induction N with
    | zero => intro j hj f hf; exact base j (by omega) f hf
    | succ N ih =>
      intro j hj f hf
      by_cases hjd : j ≤ d
      · exact base j hjd f hf
      · push Not at hjd
        rw [← hMj]
        have hsup := compFil_le_iSup hI hmax h𝔭 hd hw hjd hf
        refine (iSup₂_le fun l hl => ?_ : _ ≤ Mj j) hsup
        rw [Ideal.mul_le]
        intro a ha b hb
        rw [hMj]
        have hl' := Finset.mem_Icc.1 hl
        have h1 := base l (by omega) a ha
        have h2 := ih (j - l) (by push_cast at hj ⊢; omega) b hb
        have : (LaurentPolynomial.C (a * b) * T j : A[T;T⁻¹]) =
            (LaurentPolynomial.C a * T l) * (LaurentPolynomial.C b * T (j - l)) := by
          rw [map_mul, show j = l + (j - l) by ring, T_add]
          ring_nf
        rw [this]; exact R'.mul_mem h1 h2
  exact main j.toNat j (Int.self_le_toNat j) f hf

/-- **The extended Rees algebra is generated by `reesGenSet`.** -/
theorem reesAlg_eq_adjoin :
    ReesAlg (compFil hI hmax h𝔭 d) = Algebra.adjoin A (reesGenSet hI hmax h𝔭 d) := by
  apply le_antisymm
  · intro p hp
    have hp' : p = ∑ j ∈ p.coeff.support, LaurentPolynomial.C (p.coeff j) * T j := by
      conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [single_eq_C_mul_T]
    rw [hp']
    exact Subalgebra.sum_mem _ fun j _ => C_mul_T_mem_adjoin hI hmax h𝔭 d hd hw j _ (hp j)
  · rw [Algebra.adjoin_le_iff]
    exact reesGenSet_subset hI hmax h𝔭 d

/-- **The extended Rees algebra is of finite type.** -/
theorem reesAlg_finiteType : Algebra.FiniteType A (ReesAlg (compFil hI hmax h𝔭 d)) := by
  have hfg : (ReesAlg (compFil hI hmax h𝔭 d)).FG := by
    rw [reesAlg_eq_adjoin hI hmax h𝔭 d hd hw]
    exact Subalgebra.fg_def.2 ⟨_, reesGenSet_finite hI hmax h𝔭 d, rfl⟩
  exact (Subalgebra.fg_iff_finiteType _).1 hfg

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

instance laurent_tower {B : Type*} [CommRing B] : IsScalarTower B (Polynomial B) B[T;T⁻¹] :=
  IsScalarTower.of_algebraMap_eq fun b => by
    rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show LaurentPolynomial.C b = Polynomial.toLaurent (Polynomial.C b)
    rw [Polynomial.toLaurent_C]

/-- Laurent polynomials over a formally smooth `ℚ`-algebra are formally smooth. -/
instance laurent_formallySmooth {B : Type*} [CommRing B] [Algebra ℚ B] [Algebra.FormallySmooth ℚ B] :
    Algebra.FormallySmooth ℚ B[T;T⁻¹] := by
  have : Algebra.FormallySmooth (Polynomial B) B[T;T⁻¹] :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial B))
  have : Algebra.FormallySmooth B B[T;T⁻¹] := Algebra.FormallySmooth.comp B (Polynomial B) B[T;T⁻¹]
  exact Algebra.FormallySmooth.comp ℚ B B[T;T⁻¹]

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- The localized Rees algebras are formally smooth. -/
theorem reesLoc_formallySmooth (𝔪 : Ideal A) [𝔪.IsMaximal] :
    Algebra.FormallySmooth ℚ (ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪))) := by
  set Φ' := (compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)
  by_cases h𝔭𝔪 : 𝔭 ≤ 𝔪
  · have hZ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
    obtain ⟨n, e, ⟨⟨J, hJ, hJe⟩, hmin⟩, hev⟩ := hZ.2
    have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
    have := residueField_isIntegral 𝔪
    obtain ⟨k, ck, hrun, -, -, hsupp⟩ := hJi.exists_run (Iloc_ne_bot hI 𝔪) (Iloc_le hZ.1) J.c
      J.centred
    have hkn : k ≤ n := hrun.stage_le (Nat.zero_le _)
    have hw' : ∀ i : Fin n, ∃ w : ℕ, (w : ℚ) = d * J.e i := fun i => by
      obtain ⟨w, hw⟩ := hw i
      refine ⟨w, ?_⟩
      rw [hw, ← hev, hJe, ext0_apply]
    choose w hwe using hw'
    have hF : ∀ j, Φ'.F j = chartFil J.c J.e d j := fun j => by
      rw [compFil_loc_F hI hmax h𝔭 d 𝔪 h𝔭𝔪, cRF_eq hI hZ.1 hJ hJi]; rfl
    exact rees_formallySmooth J.c J.centred hF J.nonneg hd hwe hkn hsupp
  · have htop : ReesAlg Φ' = ⊤ := by
      rw [eq_top_iff]
      intro p _ j
      show p.coeff j ∈ ((compFil hI hmax h𝔭 d).F j).map _
      rw [compFil_F, compF_map_of_not_le hI hmax h𝔭 hd hw 𝔪 h𝔭𝔪]; trivial
    exact Algebra.FormallySmooth.of_equiv
      (((Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv).restrictScalars ℚ).symm

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

theorem rees_finitePresentation :
    Algebra.FinitePresentation ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := by
  have := reesAlg_finiteType hI hmax h𝔭 d hd hw
  have : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  exact Algebra.FinitePresentation.of_finiteType.1 inferInstance

/-- **The extended Rees algebra is smooth over `ℚ`.** -/
theorem rees_smooth : Algebra.Smooth ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := by
  set Φ := compFil hI hmax h𝔭 d
  set R := ReesAlg Φ
  have := rees_finitePresentation hI hmax h𝔭 hd hw
  refine ⟨?_, inferInstance⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro P
  show Algebra.FormallySmooth ℚ (Localization.AtPrime P.asIdeal)
  set 𝔮 := P.asIdeal.comap (algebraMap A R)
  have : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨𝔪, h𝔪, h𝔮𝔪⟩ := Ideal.exists_le_maximal 𝔮 (Ideal.IsPrime.ne_top ‹_›)
  have := h𝔪
  set Rm := ReesAlg (Φ.loc (Localization.AtPrime 𝔪))
  let : Algebra R Rm := (reesMap Φ (Localization.AtPrime 𝔪)).toAlgebra
  set M := 𝔪.primeCompl.map (algebraMap A R)
  have : IsLocalization M Rm :=
    reesMap_isLocalization Φ (Localization.AtPrime 𝔪) 𝔪.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors 𝔪)
  have : Algebra.FormallySmooth ℚ Rm := reesLoc_formallySmooth hI hmax h𝔭 hd hw 𝔪
  have hdisj : Disjoint (M : Set R) (P.asIdeal : Set R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haP
    exact ha (h𝔮𝔪 haP)
  set P' := P.asIdeal.map (algebraMap R Rm)
  have hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M Rm _ P.isPrime hdisj
  have hcomap : P'.comap (algebraMap R Rm) = P.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint M Rm P.isPrime hdisj
  have : IsLocalization P.asIdeal.primeCompl (Localization.AtPrime P') := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime P') P'
    have he : (P'.under R).primeCompl = P.asIdeal.primeCompl := by
      ext x; show x ∉ P'.comap (algebraMap R Rm) ↔ x ∉ P.asIdeal; rw [hcomap]
    exact he ▸ h
  have hT : Algebra.FormallySmooth ℚ (Localization.AtPrime P') := inferInstance
  let e0 := IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P')
    (Localization.AtPrime P.asIdeal)
  let e : Localization.AtPrime P' ≃ₐ[ℚ] Localization.AtPrime P.asIdeal :=
    AlgEquiv.ofRingEquiv (f := e0.toRingEquiv) (fun q => RingHom.map_rat_algebraMap e0.toRingEquiv.toRingHom q)
  exact @Algebra.FormallySmooth.of_equiv ℚ _ (Localization.AtPrime P') (Localization.AtPrime P.asIdeal)
    _ _ _ _ hT e

end BezoutCounterexample.Principalization

