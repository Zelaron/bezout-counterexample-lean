import BezoutCounterexample.Principalization.Spread

/-!
# Local structure of the invariant

Charts on basic opens of smooth algebras (`exists_chart_away`), explicit recentring
(`exists_centred_transport`), and `local_structure`: around every point of `V(I)` the invariant is
bounded below by the weights of one run on a basic open, with equality only for the transported
centre (upper semicontinuity and local constancy, Brais, Prop. 4.1.1). Used for Theorem 3.3 (3)
of the paper.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open KaehlerDifferential

/-- A basis of `Ω[S⁄ℚ]` consisting of differentials gives a chart. -/
def Chart.ofBasis {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}
    (b : Module.Basis (Fin n) S Ω[S⁄ℚ]) (s : Fin n → S) (hs : ∀ i, KaehlerDifferential.D ℚ S (s i) = b i) :
    Chart S n where
  x := s
  d i := (b.coord i).compDer (KaehlerDifferential.D ℚ S)
  d_x i j := by
    change b.coord i (KaehlerDifferential.D ℚ S (s j)) = _
    rw [hs, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp_all [eq_comm]
  span := by
    rw [show (fun i => KaehlerDifferential.D ℚ S (s i)) = b from funext hs, b.span_eq]

/-- **Charts exist locally** on a smooth `ℚ`-algebra: around every prime there is a basic open
`D(f)` carrying a chart. -/
theorem exists_chart_away {A : Type} [CommRing A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
    (p : Ideal A) [p.IsPrime] :
    ∃ f : A, f ∉ p ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n) := by
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℚ p
  refine ⟨f, hf, ?_⟩
  obtain ⟨-, I, b, hb⟩ := (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential).1 hstd
  have hu : IsUnit (algebraMap A (Localization.AtPrime p) f) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl)
  have : Nontrivial (Localization.Away f) := (IsLocalization.Away.lift f hu).domain_nontrivial
  have : Finite I := Module.Finite.finite_basis b
  have := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let b' := b.reindex e
  choose s hs using fun i : Fin (Fintype.card I) => hb ⟨e.symm i, rfl⟩
  exact ⟨Fintype.card I, ⟨Chart.ofBasis b' s fun i => by rw [hs]; simp [b']⟩⟩

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

variable {A : Type} [CommRing A] [Algebra ℚ A] (𝔪 : Ideal A) [𝔪.IsMaximal]

instance fs_localization [Algebra.FormallySmooth ℚ A] :
    Algebra.FormallySmooth ℚ (Localization.AtPrime 𝔪) :=
  Algebra.FormallySmooth.comp ℚ A (Localization.AtPrime 𝔪)

lemma residueField_isIntegral [Algebra.FiniteType ℚ A] :
    Algebra.IsIntegral ℚ (ResidueField (Localization.AtPrime 𝔪)) := by
  let := Ideal.Quotient.field 𝔪
  have hfin : Module.Finite ℚ (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ 𝔪)
  have hint : Algebra.IsIntegral ℚ (A ⧸ 𝔪) := Algebra.IsIntegral.of_finite ℚ _
  exact Algebra.IsIntegral.of_surjective (IsScalarTower.toAlgHom ℚ (A ⧸ 𝔪) 𝔪.ResidueField)
    𝔪.bijective_algebraMap_quotient_residueField.surjective

instance fe_residueField [Algebra.FiniteType ℚ A] :
    Algebra.FormallyEtale ℚ (ResidueField (Localization.AtPrime 𝔪)) := by
  have := residueField_isIntegral 𝔪
  exact Algebra.FormallyEtale.of_isSeparable ℚ _

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalization IsLocalRing Polynomial

namespace Chart

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} [IsLocalRing R]

/-- The recentred functions `Pᵢ(xᵢ)`, `Pᵢ` the minimal polynomial of the residue of `xᵢ`. -/
def recFun (c : Chart R n) (i : Fin n) : R := aeval (c.x i) (minpoly ℚ (residue R (c.x i)))

lemma recFun_jac (c : Chart R n) :
    c.jac c.recFun = Matrix.diagonal fun j => aeval (c.x j) (derivative (minpoly ℚ (residue R (c.x j)))) := by
  ext i j
  simp only [jac, Matrix.of_apply, recFun, Derivation.map_aeval, c.d_x, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Matrix.diagonal_apply]
  split_ifs <;> simp_all

lemma recFun_det_isUnit [Algebra.IsIntegral ℚ (ResidueField R)] (c : Chart R n) :
    IsUnit (c.jac c.recFun).det := by
  have hmap : ∀ (a : R) (p : ℚ[X]), residue R (aeval a p) = aeval (residue R a) p := fun a p =>
    (Polynomial.aeval_algebraMap_apply (B := ResidueField R) a p).symm
  rw [recFun_jac, Matrix.det_diagonal, IsUnit.prod_univ_iff]
  intro j
  rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, hmap]
  exact (Algebra.IsSeparable.isSeparable ℚ (residue R (c.x j))).aeval_derivative_ne_zero
    (minpoly.aeval ℚ _)

lemma recFun_mem [Algebra.IsIntegral ℚ (ResidueField R)] (c : Chart R n) (i : Fin n) :
    c.recFun i ∈ maximalIdeal R := by
  rw [← residue_eq_zero_iff, recFun]
  change algebraMap R (ResidueField R) _ = 0
  rw [← Polynomial.aeval_algebraMap_apply]
  exact minpoly.aeval ℚ _

end Chart

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [IsNoetherianRing A]

omit [IsDomain A] [IsNoetherianRing A] in
lemma Loc.map_aeval {M N : Submonoid A} (h : M ≤ N) (a : Localization M) (p : ℚ[X]) :
    Loc.map h (aeval a p) = aeval (Loc.map h a) p :=
  (Polynomial.aeval_algHom_apply (Loc.map h).toRatAlgHom a p).symm

/-- **Recentring over a localization**: after a controlled localization, a chart over `M⁻¹A`
can be changed so that its transport to `A_𝔪` is centred. -/
lemma exists_centred_transport [Algebra.FormallySmooth ℚ A] [Algebra.FiniteType ℚ A]
    (𝔪 : Ideal A) [𝔪.IsMaximal] {n : ℕ} {M : Submonoid A} (hM : M ≤ 𝔪.primeCompl)
    (c : Chart (Localization M) n) :
    ∃ M', ∃ hE : Loc.Ext M 𝔪.primeCompl M', ∃ c₁ : Chart (Localization M') n,
      (Loc.transport hE.le₂ c₁).IsCentred := by
  classical
  have := residueField_isIntegral 𝔪
  have hN := Ideal.primeCompl_le_nonZeroDivisors 𝔪
  set cN := Loc.transport hM c
  -- the recentred functions, over `M⁻¹A`
  set y₀ : Fin n → Localization M := fun i =>
    aeval (c.x i) (minpoly ℚ (residue _ (cN.x i))) with hy₀
  have hy : ∀ i, Loc.map hM (y₀ i) = cN.recFun i := fun i => by
    rw [hy₀]; simp only [Loc.map_aeval, Chart.recFun]; rfl
  have hdet : Loc.map hM (c.jac y₀).det = (cN.jac cN.recFun).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Chart.jac, Matrix.of_apply,
      ← Loc.transport_d, ← hy]
    rfl
  obtain ⟨M', hE, hunit⟩ := Loc.spread_isUnit hM hN (hdet ▸ cN.recFun_det_isUnit)
  set c' := Loc.transport hE.le₁ c
  have hjac : (c'.jac (fun i => Loc.map hE.le₁ (y₀ i))).det = Loc.map hE.le₁ (c.jac y₀).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Chart.jac, Matrix.of_apply, c',
      Loc.transport_d]
  refine ⟨M', hE, c'.change _ (hjac ▸ hunit), Chart.isCentred_of_mem fun i => ?_⟩
  rw [Loc.transport_x, Chart.change_x, Loc.map_apply_comp, hy]
  exact cN.recFun_mem i

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalization IsLocalRing

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **Local structure of the invariant** (upper semicontinuity and local constancy of the
maximal admissible centre, Brais, Prop. 4.1.1): around every point `𝔪 ∈ V(I)` there is a basic open
`D(g)` and a Method-1 run over a localization `M'⁻¹A` (controlled by `g`) whose final weights `ek`
bound the admissible centres at every point of `D(g)` from below, with equality exactly for
centres with the same weighted ideals as the transported final chart. -/
theorem local_structure (I : Ideal A) (hI : I ≠ ⊥) (𝔪 : Ideal A) [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) :
    ∃ (n : ℕ) (M' : Submonoid A) (g : A), g ∉ 𝔪 ∧ ∃ hctrl : Loc.Ctrl M' g,
      ∃ (k : ℕ) (ck : Chart (Localization M') n) (ek : Fin n → ℚ),
      (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧
      I.map (algebraMap A (Localization M')) ≤ ck.RF ek 1 ∧
      ∃ hM' : M' ≤ 𝔪.primeCompl, (Loc.transport hM' ck).IsCentred ∧
      ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal] (hg' : g ∉ 𝔪'),
        ∀ J' : MC (Localization.AtPrime 𝔪') n,
          J'.Adm (I.map (algebraMap A (Localization.AtPrime 𝔪'))) →
          toLex ek ≤ toLex J'.e ∧
          (J'.e = ek → ∀ t, J'.RF t = (Loc.transport (hctrl 𝔪' hg') ck).RF ek t) := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  obtain ⟨f, hf, n, ⟨c₀⟩⟩ := exists_chart_away 𝔪
  have hM₀ : Submonoid.powers f ≤ 𝔪.primeCompl := (Submonoid.powers_le).2 hf
  obtain ⟨M₁, hE₁, c₁, hc₁⟩ := exists_centred_transport 𝔪 hM₀ c₀
  -- Method 1 at `𝔪`
  set IR := I.map (algebraMap A (Localization.AtPrime 𝔪))
  have hIR : IR ≠ ⊥ := by
    intro h
    apply hI
    rw [eq_bot_iff]
    intro a ha
    have : algebraMap A (Localization.AtPrime 𝔪) a = 0 := by
      rw [← Ideal.mem_bot, ← h]; exact Ideal.mem_map_of_mem _ ha
    rw [Ideal.mem_bot]
    exact (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔪)) (by rw [this, map_zero])
  have hIRm : IR ≤ maximalIdeal (Localization.AtPrime 𝔪) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a]
    exact hI𝔪 ha
  have hSA0 := MC.sa_zero hIR hIRm _ hc₁
  obtain ⟨M', hE, k, ck, ek, hrun, hadm, hsupp, hnn, hanti, hcent⟩ :=
    spread_run 𝔪 I (n - 0) 0 rfl M₁ hE₁.le₂ c₁ 0 hc₁ (fun _ => le_rfl) (fun _ _ _ => le_rfl) hSA0
  -- control
  obtain ⟨t₁, ht₁, hct₁⟩ := hE₁.ctrl
  obtain ⟨t₂, ht₂, hct₂⟩ := hE.ctrl
  have hctrl : Loc.Ctrl M' (f * t₁ * t₂) := hct₂ _ (hct₁ f (Loc.ctrl_powers f))
  have hg : f * t₁ * t₂ ∉ 𝔪 := 𝔪.primeCompl.mul_mem (𝔪.primeCompl.mul_mem hf ht₁) ht₂
  refine ⟨n, M', f * t₁ * t₂, hg, hctrl, k, ck, ek, hsupp, hnn, hanti, hadm, hE.le₂, hcent,
    fun 𝔪' _ hg' J' hJ' => ?_⟩
  -- transfer to `𝔪'`
  have hM'𝔪' : M' ≤ 𝔪'.primeCompl := hctrl 𝔪' hg'
  set ψ := Loc.map hM'𝔪'
  have hcompat := Loc.compat_transport hM'𝔪' (Loc.transport hE.le₁ c₁)
  obtain ⟨ck'', hck'', hbound⟩ := hrun.transfer_bound hcompat
  have hIψ : (I.map (algebraMap A (Localization M'))).map ψ =
      I.map (algebraMap A (Localization.AtPrime 𝔪')) := Loc.map_map_algebraMap hM'𝔪' I
  have hck : ck'' = Loc.transport hM'𝔪' ck :=
    Chart.eq_of_x (funext fun i => by
      have := hck''.x i
      simpa [pushIdx, Fin.castLE_refl] using this)
  obtain ⟨h1, h2⟩ := hbound J' (by rw [hIψ]; exact hJ')
  rw [pad_refl] at h1 h2
  refine ⟨h1, fun he t => ?_⟩
  rw [h2 he t, hck]

end BezoutCounterexample.Principalization

