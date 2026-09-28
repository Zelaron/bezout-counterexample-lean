import BezoutCounterexample.Principalization.ReesSmooth

/-!
# The invariant at a point

Theorem 3.3 (1), (2), (5) (`thm:invariant`) of the paper, at a single point.

* `IsInv`: the invariant of an ideal on a local ring (lexicographically minimal weights of an
  admissible marked centre), its uniqueness, and its computation by Method-1 runs.
* `Chart.card_eq`: all charts on a ring have the same size.
* `IsInv.mapEquiv`: invariance under isomorphisms; `Chart.mvPolynomial`: polynomial charts.
* `IsInv.transfer`: **smooth invariance** of the invariant.
* `IsRun.goodV`, `encW_lt`: Method-1 weights lie in a well-ordered set (termination).
* `IsInv.eq_zero_of_derivations`: the length bound.
* `Chart.IsCentred.span_x_isPrime`: initial coordinates of a centred chart generate a prime.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open IsLocalRing

section Inv

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}

/-- `e` is the *invariant* of `I` on the local ring `S`: the lexicographically minimal weights of
an admissible marked centre (charts of size `n`). -/
def IsInv (I : Ideal S) (n : ℕ) (e : Fin n → ℚ) : Prop :=
  (∃ J : MC S n, J.Adm I ∧ J.e = e) ∧ ∀ J' : MC S n, J'.Adm I → toLex e ≤ toLex J'.e

lemma IsInv.unique {I : Ideal S} {e e' : Fin n → ℚ} (h : IsInv I n e) (h' : IsInv I n e') :
    e = e' := by
  obtain ⟨⟨J, hJ, rfl⟩, h1⟩ := h
  obtain ⟨⟨J', hJ', rfl⟩, h2⟩ := h'
  exact toLex.injective (le_antisymm (h1 J' hJ') (h2 J hJ))

lemma IsInv.nonneg {I : Ideal S} {e : Fin n → ℚ} (h : IsInv I n e) (i : Fin n) : 0 ≤ e i := by
  obtain ⟨⟨J, -, rfl⟩, -⟩ := h
  exact J.nonneg i

lemma IsInv.anti {I : Ideal S} {e : Fin n → ℚ} (h : IsInv I n e) : Antitone e := by
  obtain ⟨⟨J, -, rfl⟩, -⟩ := h
  exact J.anti

variable [IsNoetherianRing S]

/-- A run from a centred chart ending in an admissible centred chart computes the invariant. -/
lemma IsInv.of_run {I : Ideal S} {c : Chart S n} {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ}
    (hrun : IsRun I 0 c 0 k ck ek) (hadm : I ≤ ck.RF ek 1) (hck : ck.IsCentred)
    (hnn : ∀ i, 0 ≤ ek i) (hanti : Antitone ek) : IsInv I n ek := by
  refine ⟨⟨⟨ck, ek, hck, hnn, hanti⟩, hadm, rfl⟩, fun J' hJ' => ?_⟩
  obtain ⟨_, _, hb⟩ := hrun.transfer_bound (Compat.id c)
  have := (hb J' (by rw [Ideal.map_id]; exact hJ')).1
  rwa [pad_refl] at this


lemma exists_isInv {I : Ideal S} (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S) (c : Chart S n)
    (hc : c.IsCentred) : ∃ e, IsInv I n e := by
  obtain ⟨J, hJ, hmax⟩ := MC.exists_max hI hIm c hc
  exact ⟨J.e, ⟨J, hJ, rfl⟩, fun J' hJ' => (hmax J' hJ').1⟩

/-- Every centred chart starts a run computing the invariant. -/
lemma IsInv.exists_run {I : Ideal S} (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S) {e : Fin n → ℚ}
    (he : IsInv I n e) (c : Chart S n) (hc : c.IsCentred) :
    ∃ (k : ℕ) (ck : Chart S n), IsRun I 0 c 0 k ck e ∧ I ≤ ck.RF e 1 ∧ ck.IsCentred ∧
      (∀ i, e i ≠ 0 ↔ (i : ℕ) < k) := by
  obtain ⟨k, ck, ek, hrun, hadm, hck, hnn, hanti, hsupp⟩ := MC.exists_run hI hIm c hc
  obtain rfl := (IsInv.of_run hrun hadm hck hnn hanti).unique he
  exact ⟨k, ck, hrun, hadm, hck, hsupp⟩

end Inv

section Size

/-- **All charts on a nontrivial ring have the same size** (the rank of `Ω`). -/
lemma Chart.card_eq {S : Type*} [CommRing S] [Algebra ℚ S] [Nontrivial S] {n n' : ℕ}
    (c : Chart S n) (c' : Chart S n') : n = n' := by
  have := c.basis.indexEquiv c'.basis
  simpa using Fintype.card_congr this

end Size

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

section Equiv

variable {S S' : Type*} [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] {n : ℕ}

/-- Conjugating a derivation by an isomorphism. -/
def conjDer (φ : S ≃ₐ[ℚ] S') (δ : Derivation ℚ S S) : Derivation ℚ S' S' :=
  Derivation.mk' (φ.toLinearMap ∘ₗ (δ : S →ₗ[ℚ] S) ∘ₗ φ.symm.toLinearMap) (fun a b => by
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      map_mul, Derivation.leibniz, smul_eq_mul, map_add, Derivation.coeFn_coe,
      AlgEquiv.apply_symm_apply])

@[simp] lemma conjDer_apply (φ : S ≃ₐ[ℚ] S') (δ : Derivation ℚ S S) (a : S) :
    conjDer φ δ (φ a) = φ (δ a) := by
  change φ.toLinearMap (δ (φ.symm.toLinearMap (φ a))) = φ (δ a)
  simp

/-- Transport of a chart along a `ℚ`-algebra isomorphism. -/
def Chart.mapEquiv (φ : S ≃ₐ[ℚ] S') (c : Chart S n) : Chart S' n where
  x i := φ (c.x i)
  d i := conjDer φ (c.d i)
  d_x i j := by rw [conjDer_apply, c.d_x]; split_ifs <;> simp
  span := by
    let : Algebra S S' := (φ : S →+* S').toAlgebra
    have : IsScalarTower ℚ S S' := IsScalarTower.of_algebraMap_eq fun q => by
      show algebraMap ℚ S' q = φ (algebraMap ℚ S q)
      rw [AlgEquiv.commutes]
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := φ.surjective b
    have h1 : KaehlerDifferential.D ℚ S' (φ a) =
        KaehlerDifferential.map ℚ ℚ S S' (KaehlerDifferential.D ℚ S a) := by
      rw [KaehlerDifferential.map_D]; rfl
    rw [h1, c.kD_eq_sum a, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, KaehlerDifferential.map_D]
    rw [← algebraMap_smul S' ((c.d j) a)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

@[simp] lemma Chart.mapEquiv_x (φ : S ≃ₐ[ℚ] S') (c : Chart S n) (i : Fin n) :
    (c.mapEquiv φ).x i = φ (c.x i) := rfl

lemma Chart.mapEquiv_RF (φ : S ≃ₐ[ℚ] S') (c : Chart S n) (e : Fin n → ℚ) (t : ℚ) :
    (c.mapEquiv φ).RF e t = (c.RF e t).map φ := by
  rw [Chart.RF, Chart.RF, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨α, h0, ht, rfl⟩
    exact ⟨∏ i, c.x i ^ α i, ⟨α, h0, ht, rfl⟩, by simp [map_prod, map_pow]⟩
  · rintro ⟨_, ⟨α, h0, ht, rfl⟩, rfl⟩
    exact ⟨α, h0, ht, by simp [map_prod, map_pow]⟩

variable [IsLocalRing S] [IsLocalRing S']

lemma Chart.IsCentred.mapEquiv {c : Chart S n} (hc : c.IsCentred) (φ : S ≃ₐ[ℚ] S') :
    (c.mapEquiv φ).IsCentred := by
  have hm : maximalIdeal S' = (maximalIdeal S).map φ := by
    have : ((maximalIdeal S).map φ).IsMaximal := Ideal.map_isMaximal_of_equiv φ
    exact (eq_maximalIdeal this).symm
  rw [Chart.IsCentred, hm, hc, Ideal.map_span]
  congr 1
  ext f
  simp [Set.mem_image, Set.mem_range]

/-- Transport of a marked centre. -/
def MC.mapEquiv (φ : S ≃ₐ[ℚ] S') (J : MC S n) : MC S' n :=
  ⟨J.c.mapEquiv φ, J.e, J.centred.mapEquiv φ, J.nonneg, J.anti⟩

lemma MC.Adm.mapEquiv {I : Ideal S} {J : MC S n} (h : J.Adm I) (φ : S ≃ₐ[ℚ] S') :
    (J.mapEquiv φ).Adm (I.map φ) := by
  show I.map φ ≤ (J.c.mapEquiv φ).RF J.e 1
  rw [Chart.mapEquiv_RF]
  exact Ideal.map_mono h

omit [IsLocalRing S] [IsLocalRing S'] in
lemma map_map_symm (φ : S ≃ₐ[ℚ] S') (I : Ideal S) : (I.map φ).map φ.symm = I := by
  refine le_antisymm ?_ fun a ha => ?_
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    simpa using ha
  · have : φ.symm (φ a) ∈ (I.map φ).map φ.symm :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    simpa using this

/-- **Invariants are transported along isomorphisms.** -/
lemma IsInv.mapEquiv {I : Ideal S} {e : Fin n → ℚ} (h : IsInv I n e) (φ : S ≃ₐ[ℚ] S') :
    IsInv (I.map φ) n e := by
  obtain ⟨⟨J, hJ, rfl⟩, hmin⟩ := h
  refine ⟨⟨J.mapEquiv φ, hJ.mapEquiv φ, rfl⟩, fun J' hJ' => ?_⟩
  have := hmin (J'.mapEquiv φ.symm) (by
    have h2 := hJ'.mapEquiv φ.symm
    rwa [map_map_symm] at h2)
  exact this

end Equiv

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

section MvPoly

open MvPolynomial

variable {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ} (r : ℕ)

/-- The coordinates of the polynomial chart on `S[X₀, …, X_{r-1}]`. -/
def mvX (c : Chart S n) : Fin (n + r) → MvPolynomial (Fin r) S :=
  Fin.append (fun i => C (c.x i)) (fun j => X j)

/-- The derivations of the polynomial chart. -/
def mvD (c : Chart S n) :
    Fin (n + r) → Derivation ℚ (MvPolynomial (Fin r) S) (MvPolynomial (Fin r) S) :=
  Fin.append (fun i => BezoutCounterexample.mapCoeffs (c.d i))
    (fun j => (pderiv j : Derivation S (MvPolynomial (Fin r) S) _).restrictScalars ℚ)

@[simp] lemma mvX_castAdd (c : Chart S n) (i : Fin n) : mvX r c (Fin.castAdd r i) = C (c.x i) := by
  simp [mvX]

@[simp] lemma mvX_natAdd (c : Chart S n) (j : Fin r) : mvX r c (Fin.natAdd n j) = X j := by
  simp [mvX]

@[simp] lemma mvD_castAdd (c : Chart S n) (i : Fin n) :
    mvD r c (Fin.castAdd r i) = BezoutCounterexample.mapCoeffs (c.d i) := by
  simp [mvD]

@[simp] lemma mvD_natAdd (c : Chart S n) (j : Fin r) :
    mvD r c (Fin.natAdd n j) = (pderiv j : Derivation S (MvPolynomial (Fin r) S) _).restrictScalars ℚ := by
  simp [mvD]

lemma castAdd_ne_natAdd' {m : ℕ} (a : Fin m) (b : Fin r) : Fin.castAdd r a ≠ Fin.natAdd m b :=
  fun h => by have := congrArg Fin.val h; simp at this; omega

lemma mvD_mvX (c : Chart S n) (i j : Fin (n + r)) :
    mvD r c i (mvX r c j) = if i = j then 1 else 0 := by
  classical
  cases i using Fin.addCases with
  | left a =>
    cases j using Fin.addCases with
    | left b =>
      rw [mvD_castAdd, mvX_castAdd, BezoutCounterexample.mapCoeffs_C, c.d_x]
      by_cases h : a = b
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (Fin.castAdd_injective _ _ h')), map_zero]
    | right b =>
      rw [mvD_castAdd, mvX_natAdd, BezoutCounterexample.mapCoeffs_X,
        ite_eq_right (castAdd_ne_natAdd' r a b)]
  | right a =>
    cases j using Fin.addCases with
    | left b =>
      rw [mvD_natAdd, mvX_castAdd, ite_eq_right (castAdd_ne_natAdd' r b a).symm]
      simp
    | right b =>
      rw [mvD_natAdd, mvX_natAdd]
      simp only [Derivation.restrictScalars_apply, pderiv_X]
      by_cases h : a = b
      · subst h; simp
      · rw [ite_eq_right (fun h' => h (Fin.natAdd_injective _ _ h')), Pi.single_eq_of_ne' h]

lemma span_mvPolynomial (c : Chart S n) :
    Submodule.span (MvPolynomial (Fin r) S) (Set.range fun i : Fin (n + r) =>
      KaehlerDifferential.D ℚ (MvPolynomial (Fin r) S) (mvX r c i)) = ⊤ := by
  set W := Submodule.span (MvPolynomial (Fin r) S) (Set.range fun i : Fin (n + r) =>
      KaehlerDifferential.D ℚ (MvPolynomial (Fin r) S) (mvX r c i))
  have hX : ∀ j, KaehlerDifferential.D ℚ (MvPolynomial (Fin r) S) (X j) ∈ W := fun j =>
    Submodule.subset_span ⟨Fin.natAdd n j, by simp⟩
  have hC : ∀ a : S, KaehlerDifferential.D ℚ (MvPolynomial (Fin r) S) (C a) ∈ W := by
    intro a
    have h1 : KaehlerDifferential.D ℚ (MvPolynomial (Fin r) S) (C a) =
        KaehlerDifferential.map ℚ ℚ S (MvPolynomial (Fin r) S) (KaehlerDifferential.D ℚ S a) := by
      rw [KaehlerDifferential.map_D]; rfl
    rw [h1, c.kD_eq_sum a, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, KaehlerDifferential.map_D]
    rw [← algebraMap_smul (MvPolynomial (Fin r) S) ((c.d j) a), MvPolynomial.algebraMap_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castAdd r j, by simp⟩)
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add]; exact W.add_mem hp hq
  | mul_X p j ih =>
    rw [Derivation.leibniz]
    exact W.add_mem (W.smul_mem _ (hX j)) (W.smul_mem _ ih)

/-- **The polynomial chart** `(x, X)` on `S[X₀, …, X_{r-1}]`. -/
def Chart.mvPolynomial (c : Chart S n) : Chart (MvPolynomial (Fin r) S) (n + r) where
  x := mvX r c
  d := mvD r c
  d_x := mvD_mvX r c
  span := span_mvPolynomial r c

lemma Chart.compat_mvPolynomial (c : Chart S n) :
    Compat (Nat.le_add_right n r) (C : S →+* MvPolynomial (Fin r) S) c (c.mvPolynomial r) := by
  refine ⟨fun i => ?_, fun i f => ?_, fun i hi f => ?_⟩
  · exact mvX_castAdd r c i
  · show mvD r c (Fin.castAdd r i) (C f) = C (c.d i f)
    rw [mvD_castAdd, BezoutCounterexample.mapCoeffs_C]
  · cases i using Fin.addCases with
    | left a => exact absurd hi (by simp)
    | right a =>
      show mvD r c (Fin.natAdd n a) (C f) = 0
      rw [mvD_natAdd]
      simp

end MvPoly

section CompatLemmas

variable {S : Type*} [CommRing S] [Algebra ℚ S] {S' : Type*} [CommRing S'] [Algebra ℚ S']
  {S'' : Type*} [CommRing S''] [Algebra ℚ S''] {n n' n'' : ℕ}

lemma Chart.compat_localization {L : Type*} [CommRing L] [Algebra ℚ L] [Algebra S L]
    [IsScalarTower ℚ S L] (M : Submonoid S) [IsLocalization M L] (c : Chart S n) :
    Compat (le_refl n) (algebraMap S L) c (c.localization M) := by
  refine ⟨fun i => ?_, fun i f => ?_, fun i hi f => absurd i.2 (by omega)⟩
  · simp [Fin.castLE_refl]
  · simp only [Fin.castLE_refl]
    exact Chart.localization_d M c i f

lemma Compat.trans {hnn : n ≤ n'} {hnn' : n' ≤ n''} {ψ : S →+* S'} {ψ' : S' →+* S''}
    {c : Chart S n} {c' : Chart S' n'} {c'' : Chart S'' n''} (h : Compat hnn ψ c c')
    (h' : Compat hnn' ψ' c' c'') : Compat (hnn.trans hnn') (ψ'.comp ψ) c c'' := by
  have hcast : ∀ i : Fin n, Fin.castLE (hnn.trans hnn') i = Fin.castLE hnn' (Fin.castLE hnn i) :=
    fun i => Fin.ext rfl
  refine ⟨fun i => ?_, fun i f => ?_, fun i hi f => ?_⟩
  · rw [hcast, h'.x, h.x]; rfl
  · rw [hcast, RingHom.comp_apply, h'.d, h.d]; rfl
  · by_cases hi' : n' ≤ (i : ℕ)
    · exact h'.d_extra i hi' _
    · have hlt : (i : ℕ) < n' := by omega
      have : i = Fin.castLE hnn' ⟨i, hlt⟩ := Fin.ext rfl
      rw [this, RingHom.comp_apply, h'.d, h.d_extra ⟨i, hlt⟩ (by simpa using hi), map_zero]

lemma Compat.map_RF_le {hnn : n ≤ n'} {ψ : S →+* S'} {c : Chart S n} {c' : Chart S' n'}
    (h : Compat hnn ψ c c') (e : Fin n → ℚ) (t : ℚ) :
    (c.RF e t).map ψ ≤ c'.RF (pad n' e) t := by
  classical
  rw [Chart.RF, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨α, h0, ht, rfl⟩, rfl⟩
  apply Ideal.subset_span
  refine ⟨pushIdx hnn α, fun i hi => ?_, by rw [lam_pad]; exact ht, ?_⟩
  · by_cases hin : (i : ℕ) < n
    · have : i = Fin.castLE hnn ⟨i, hin⟩ := Fin.ext rfl
      rw [this, pushIdx_apply]
      rw [this, pad_castLE] at hi
      exact h0 _ hi
    · exact pushIdx_apply_ge hnn α i (by omega)
  · rw [map_prod]
    symm
    refine (Fintype.prod_of_injective (Fin.castLE hnn) (Fin.castLE_injective hnn) _ _
      (fun i hi => ?_) (fun i => ?_)).symm
    · have : n ≤ (i : ℕ) := by
        by_contra hlt
        exact hi ⟨⟨i, by omega⟩, rfl⟩
      rw [pushIdx_apply_ge hnn α i this, pow_zero]
    · rw [pushIdx_apply, h.x, map_pow]

end CompatLemmas

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

lemma pad_nonneg_gen {n n' : ℕ} {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (i : Fin n') :
    0 ≤ pad n' e i := by
  simp only [pad]; split_ifs; exact he _; exact le_rfl

lemma pad_antitone_gen {n n' : ℕ} {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) :
    Antitone (pad n' e) := by
  intro a b hab
  simp only [pad]
  by_cases hb : (b : ℕ) < n
  · rw [dite_eq_left hb, dite_eq_left (lt_of_le_of_lt (Fin.le_def.1 hab) hb)]
    exact hanti (Fin.le_def.2 (by simpa using Fin.le_def.1 hab))
  · rw [dite_eq_right hb]; split_ifs; exact he _; exact le_rfl

section SI

variable {S S' : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S]
  [CommRing S'] [Algebra ℚ S'] [IsLocalRing S'] [IsNoetherianRing S']
  [Algebra.FormallySmooth ℚ S'] [Algebra.FormallySmooth ℚ (ResidueField S')]
  [Algebra.IsIntegral ℚ (ResidueField S')] {n n' : ℕ}

/-- **Smooth invariance** (transfer along a local homomorphism with a compatible chart): the
invariant of `I S'` is the padded invariant of `I`. -/
theorem IsInv.transfer {hnn : n ≤ n'} {ψ : S →+* S'}
    (hψ : ∀ a ∈ maximalIdeal S, ψ a ∈ maximalIdeal S')
    {c : Chart S n} (hc : c.IsCentred) {c' : Chart S' n'} (hcc : Compat hnn ψ c c')
    {I : Ideal S} (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S) {e : Fin n → ℚ} (he : IsInv I n e) :
    IsInv (I.map ψ) n' (pad n' e) := by
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ := he.exists_run hI hIm c hc
  obtain ⟨ck', hck', hbound⟩ := hrun.transfer_bound hcc
  refine ⟨?_, fun J' hJ' => (hbound J' hJ').1⟩
  obtain ⟨c'', hc'', hx⟩ := Chart.exists_centred ck'
  have hRF : ∀ t, c''.RF (pad n' e) t = ck'.RF (pad n' e) t := by
    intro t
    refine Chart.RF_congr (fun i hi => ?_) t
    have hin : (i : ℕ) < n := by
      by_contra h
      exact hi (by simp only [pad]; rw [dite_eq_right h])
    have hi' : i = Fin.castLE hnn ⟨i, hin⟩ := Fin.ext rfl
    apply hx
    rw [hi', hck'.x]
    exact hψ _ (hck.x_mem _)
  refine ⟨⟨c'', pad n' e, hc'', pad_nonneg_gen he.nonneg, pad_antitone_gen he.nonneg he.anti⟩,
    ?_, rfl⟩
  show I.map ψ ≤ c''.RF (pad n' e) 1
  rw [hRF]
  exact (Ideal.map_mono hadm).trans (hck'.map_RF_le e 1)

end SI

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

/-- Extension of a weight vector by zeros to `ℕ → ℚ`. -/
def ext0 {n : ℕ} (e : Fin n → ℚ) : ℕ → ℚ := fun i => if h : i < n then e ⟨i, h⟩ else 0

lemma ext0_apply {n : ℕ} (e : Fin n → ℚ) (i : Fin n) : ext0 e i = e i := by
  simp [ext0]

lemma ext0_pad {n n' : ℕ} (hnn : n ≤ n') (e : Fin n → ℚ) : ext0 (pad n' e) = ext0 e := by
  funext i
  simp only [ext0, pad]
  split_ifs <;> first | rfl | omega

/-- The product of the denominators of the first `j` weights. -/
def denPN (v : ℕ → ℚ) (j : ℕ) : ℕ := ∏ i ∈ Finset.range j, (v i).den

lemma denPN_pos (v : ℕ → ℚ) (j : ℕ) : 0 < denPN v j :=
  Finset.prod_pos fun i _ => (v i).den_pos

lemma denPN_congr {v v' : ℕ → ℚ} {j : ℕ} (h : ∀ i < j, v i = v' i) : denPN v j = denPN v' j :=
  Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/-- Method-1 weights: every weight is `0` or `D!/a` for a positive integer `a`, where `D` is the
product of the denominators of the previous weights. -/
def GoodV (v : ℕ → ℚ) : Prop :=
  ∀ i, v i = 0 ∨ ∃ a : ℕ, 0 < a ∧ v i = ((denPN v i).factorial : ℚ) / a

lemma GoodV.nonneg {v : ℕ → ℚ} (h : GoodV v) (i : ℕ) : 0 ≤ v i := by
  rcases h i with h0 | ⟨a, ha, h1⟩
  · rw [h0]
  · rw [h1]; positivity

lemma dvd_den_mul_int {q : ℚ} {D : ℕ} (h : q.den ∣ D) : ∃ z : ℤ, (D : ℚ) * q = z := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨q.num * m, ?_⟩
  push_cast
  have := Rat.mul_den_eq_num q
  calc ((q.den : ℚ) * m) * q = (q * q.den) * m := by ring
    _ = q.num * m := by rw [this]

/-- The new weight of a Method-1 step is good. -/
lemma nextW_good {n j : ℕ} {e : Fin n → ℚ} (hnn : ∀ i, 0 ≤ e i)
    (hz : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0) {β : Fin n →₀ ℕ} (hlam : lam e β < 1)
    (hN : 0 < tailSum j β) :
    ∃ a : ℕ, 0 < a ∧ nextW e j β = ((denPN (ext0 e) j).factorial : ℚ) / a := by
  set D := denPN (ext0 e) j with hD
  have hDpos : 0 < D := denPN_pos _ _
  -- `D · λ` is an integer
  have hint : ∃ z : ℤ, (D : ℚ) * lam e β = z := by
    have : ∀ i : Fin n, ∃ z : ℤ, (D : ℚ) * ((β i : ℚ) * e i) = z := by
      intro i
      by_cases hij : (i : ℕ) < j
      · have hdvd : (e i).den ∣ D := by
          rw [hD, denPN]
          have : (ext0 e i).den = (e i).den := by rw [ext0_apply]
          rw [← this]
          exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hij)
        obtain ⟨z, hz'⟩ := dvd_den_mul_int hdvd
        exact ⟨β i * z, by push_cast; rw [← hz']; ring⟩
      · exact ⟨0, by rw [hz i (by omega)]; simp⟩
    choose z hz' using this
    refine ⟨∑ i, z i, ?_⟩
    rw [lam, Finset.mul_sum]; push_cast
    exact Finset.sum_congr rfl fun i _ => hz' i
  obtain ⟨z, hz'⟩ := hint
  have hlam0 : 0 ≤ lam e β := lam_nonneg hnn β
  have hzlt : z < D := by
    have : (z : ℚ) < D := by
      rw [← hz']; nlinarith [show (0 : ℚ) < D from by exact_mod_cast hDpos]
    exact_mod_cast this
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := by rw [← hz']; positivity
    exact_mod_cast this
  set m : ℕ := (D - z).toNat with hm
  have hmD : (m : ℤ) = D - z := Int.toNat_of_nonneg (by omega)
  have hm1 : 1 ≤ m := by omega
  have hmle : m ≤ D := by omega
  have hmdvd : m ∣ D.factorial := Nat.dvd_factorial (by omega) hmle
  obtain ⟨q, hq⟩ := hmdvd
  refine ⟨D * tailSum j β * q, ?_, ?_⟩
  · have : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h, mul_zero] at hq; exact absurd hq (Nat.factorial_pos D).ne'
      · exact h
    positivity
  · have hmq : ((D - z : ℤ) : ℚ) = m := by exact_mod_cast hmD.symm
    have h1 : 1 - lam e β = (m : ℚ) / D := by
      rw [← hmq]; push_cast; rw [← hz']; field_simp
    rw [nextW, h1, hq]
    have hN' : (0 : ℚ) < tailSum j β := by exact_mod_cast hN
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm1
    have hq' : (0 : ℚ) < q := by
      have : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · rw [h, mul_zero] at hq; exact absurd hq (Nat.factorial_pos D).ne'
        · exact h
      exact_mod_cast this
    push_cast
    field_simp

lemma ext0_nextE_lt {n j : ℕ} (e : Fin n → ℚ) (b : ℚ) {i : ℕ} (hi : i < j) :
    ext0 (nextE e j b) i = ext0 e i := by
  simp only [ext0, nextE]
  split_ifs <;> simp_all

/-- **Method-1 weights are good.** -/
lemma IsRun.goodV {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ} {I : Ideal S} {j : ℕ}
    {c : Chart S n} {e : Fin n → ℚ} {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ}
    (h : IsRun I j c e k ck ek) :
    (∀ i, 0 ≤ e i) → (∀ i : Fin n, j ≤ (i : ℕ) → e i = 0) →
      (∀ i < j, ext0 e i = 0 ∨ ∃ a : ℕ, 0 < a ∧
        ext0 e i = ((denPN (ext0 e) i).factorial : ℚ) / a) →
      GoodV (ext0 ek) := by
  induction h with
  | refl j c e =>
    intro _ hz hg i
    by_cases hij : i < j
    · exact hg i hij
    · left
      simp only [ext0]
      split_ifs with h
      · exact hz _ (by simp; omega)
      · rfl
  | @step j c e k ck ek hj f hf β l hl hβl hlam hN hunit hb u hu hnext ih =>
    intro hnn hz hg
    obtain ⟨a, ha, hab⟩ := nextW_good hnn hz hlam hN
    have hbpos : 0 < nextW e j β := by
      rw [hab]; positivity
    apply ih
    · intro i
      simp only [nextE]
      split_ifs
      · exact hnn i
      · exact hbpos.le
      · exact le_rfl
    · intro i hi
      simp only [nextE]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · intro i hi
      have hden : denPN (ext0 (nextE e j (nextW e j β))) i = denPN (ext0 e) i :=
        denPN_congr fun i' hi' => ext0_nextE_lt e _ (by omega)
      rw [hden]
      by_cases hij : i < j
      · rw [ext0_nextE_lt e _ hij]; exact hg i hij
      · have hieq : i = j := by omega
        subst hieq
        right
        refine ⟨a, ha, ?_⟩
        simp only [ext0, dite_eq_left hj, nextE, lt_irrefl, ite_false, ite_true]
        exact hab

lemma IsInv.goodV {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S]
    {n : ℕ} {I : Ideal S} (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S) {e : Fin n → ℚ}
    (he : IsInv I n e) (c : Chart S n) (hc : c.IsCentred) : GoodV (ext0 e) := by
  obtain ⟨k, ck, hrun, -, -, -⟩ := he.exists_run hI hIm c hc
  exact hrun.goodV (fun _ => le_rfl) (fun _ _ => rfl) (fun i hi => absurd hi (Nat.not_lt_zero _))

/-- **Length bound** for the invariant. -/
lemma IsInv.eq_zero_of_derivations {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S]
    [IsNoetherianRing S] {n : ℕ} {I : Ideal S} (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S)
    {e : Fin n → ℚ} (he : IsInv I n e) (c : Chart S n) (hc : c.IsCentred) {m : ℕ}
    (δ : Fin m → Derivation ℚ S S) (hδ : ∀ j, ∀ f ∈ I, δ j f ∈ I) (y : Fin m → S)
    (hy : IsUnit (Matrix.of fun j l => δ j (y l)).det) (i : Fin n) (hi : n ≤ (i : ℕ) + m) :
    e i = 0 := by
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ := he.exists_run hI hIm c hc
  have hkm := length_le_of_derivations hrun hadm hck he.nonneg he.anti hsupp δ hδ y hy
  by_contra hne
  have := (hsupp i).1 hne
  omega

section Measure

/-- The well-founded encoding of good weight vectors supported below `N`. -/
def encW (N : ℕ) (v : ℕ → ℚ) : Lex (Fin N → WithTop ℕ) :=
  toLex fun i => if v i = 0 then ⊤ else
    ((⌊((denPN v i).factorial : ℚ) / v i⌋₊ : ℕ) : WithTop ℕ)

lemma encW_eq_of_good {v : ℕ → ℚ} {i a : ℕ} (_ha : 0 < a)
    (hv : v i = ((denPN v i).factorial : ℚ) / a) :
    ⌊((denPN v i).factorial : ℚ) / v i⌋₊ = a := by
  have hf : (0 : ℚ) < (denPN v i).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [hv, div_div_cancel₀ hf.ne']
  exact Nat.floor_natCast a

/-- **The encoding is strictly antitone** on good vectors supported below `N`. -/
lemma encW_lt {N : ℕ} {v v' : ℕ → ℚ} (hv : GoodV v) (hv' : GoodV v')
    (hz : ∀ i, N ≤ i → v i = 0) (hz' : ∀ i, N ≤ i → v' i = 0) (hlt : toLex v < toLex v') :
    encW N v' < encW N v := by
  obtain ⟨j, hbelow, hj⟩ := hlt
  simp only [Pi.toLex_apply] at hbelow hj
  have hjN : j < N := by
    by_contra h
    rw [hz j (by omega), hz' j (by omega)] at hj
    exact lt_irrefl _ hj
  refine ⟨⟨j, hjN⟩, fun i hi => ?_, ?_⟩
  · have hi' : (i : ℕ) < j := hi
    simp only [encW, Pi.toLex_apply]
    rw [hbelow i hi', denPN_congr fun i' hi'' => hbelow i' (by omega)]
  · simp only [encW, Pi.toLex_apply]
    have hden : denPN v j = denPN v' j := denPN_congr fun i hi => hbelow i hi
    have hv'0 : v' j ≠ 0 := fun h => by
      rw [h] at hj; exact absurd hj (not_lt.2 (hv.nonneg j))
    rw [ite_eq_right hv'0]
    obtain ⟨a', ha', hva'⟩ := (hv' j).resolve_left hv'0
    rw [encW_eq_of_good ha' hva']
    by_cases hv0 : v j = 0
    · rw [ite_eq_left hv0]; exact WithTop.coe_lt_top _
    · rw [ite_eq_right hv0]
      obtain ⟨a, ha, hva⟩ := (hv j).resolve_left hv0
      rw [encW_eq_of_good ha hva]
      rw [hva, hva', hden] at hj
      have hf : (0 : ℚ) < (denPN v' j).factorial := by exact_mod_cast Nat.factorial_pos _
      have := (div_lt_div_iff_of_pos_left hf (by exact_mod_cast ha) (by exact_mod_cast ha')).1 hj
      have h2 : a' < a := by exact_mod_cast this
      exact WithTop.coe_lt_coe.2 h2

end Measure

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing MvPowerSeries

section Face

variable {n : ℕ}

/-- The indicator weights of the first `k` coordinates. -/
def indW (k : ℕ) : Fin n → ℚ := fun i => if (i : ℕ) < k then 1 else 0

lemma indW_nonneg (k : ℕ) (i : Fin n) : 0 ≤ indW k i := by
  simp only [indW]; split_ifs <;> norm_num

lemma lam_indW_lt_one {k : ℕ} {β : Fin n →₀ ℕ} :
    lam (indW k) β < 1 ↔ ∀ i : Fin n, (i : ℕ) < k → β i = 0 := by
  have hl : lam (indW k) β = ∑ i : Fin n, if (i : ℕ) < k then (β i : ℚ) else 0 := by
    simp only [lam, indW, mul_ite, mul_one, mul_zero]
  rw [hl]
  constructor
  · intro h i hi
    by_contra hne
    have h1 : (1 : ℚ) ≤ if (i : ℕ) < k then (β i : ℚ) else 0 := by
      rw [ite_eq_left hi]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
    have h2 : (if (i : ℕ) < k then (β i : ℚ) else 0) ≤ ∑ j : Fin n, if (j : ℕ) < k then (β j : ℚ) else 0 :=
      Finset.single_le_sum (f := fun j : Fin n => if (j : ℕ) < k then (β j : ℚ) else 0)
        (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
    linarith
  · intro h
    have : (∑ i : Fin n, if (i : ℕ) < k then (β i : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by split_ifs with hi <;> simp [h i, hi]
    rw [this]; norm_num

variable {K : Type*} [CommRing K]

/-- Restriction of power series to the face `X₀ = ⋯ = X_{k-1} = 0`. -/
def face (k : ℕ) (f : MvPowerSeries (Fin n) K) : MvPowerSeries (Fin n) K :=
  fun β => if ∀ i : Fin n, (i : ℕ) < k → β i = 0 then coeff β f else 0

lemma coeff_face (k : ℕ) (f : MvPowerSeries (Fin n) K) (β : Fin n →₀ ℕ) :
    coeff β (face k f) = if ∀ i : Fin n, (i : ℕ) < k → β i = 0 then coeff β f else 0 := rfl

lemma face_mul (k : ℕ) (f g : MvPowerSeries (Fin n) K) : face k (f * g) = face k f * face k g := by
  ext β
  rw [coeff_face, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 : ∀ i : Fin n, (i : ℕ) < k → p.1 i = 0 := fun i hi => by
      have := congrArg (· i) hp; simp only [Finsupp.add_apply] at this; rw [h i hi] at this; omega
    have h2 : ∀ i : Fin n, (i : ℕ) < k → p.2 i = 0 := fun i hi => by
      have := congrArg (· i) hp; simp only [Finsupp.add_apply] at this; rw [h i hi] at this; omega
    rw [coeff_face, coeff_face, ite_eq_left h1, ite_eq_left h2]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_face, coeff_face]
    push Not at h
    obtain ⟨i, hi, hne⟩ := h
    by_cases h1 : ∀ i : Fin n, (i : ℕ) < k → p.1 i = 0
    · have h2 : ¬ ∀ i : Fin n, (i : ℕ) < k → p.2 i = 0 := fun h2 => hne (by
        rw [← hp, Finsupp.add_apply, h1 i hi, h2 i hi])
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

lemma face_add (k : ℕ) (f g : MvPowerSeries (Fin n) K) : face k (f + g) = face k f + face k g := by
  ext β
  rw [coeff_face, map_add, map_add, coeff_face, coeff_face]
  split_ifs <;> simp

lemma face_one (k : ℕ) : face k (1 : MvPowerSeries (Fin n) K) = 1 := by
  ext β
  rw [coeff_face]
  split_ifs with h
  · rfl
  · rw [coeff_one, ite_eq_right]
    rintro rfl; exact h fun i _ => rfl

lemma face_zero (k : ℕ) : face k (0 : MvPowerSeries (Fin n) K) = 0 := by
  ext β; rw [coeff_face]; simp

/-- The face restriction as a ring hom. -/
def faceHom (k : ℕ) : MvPowerSeries (Fin n) K →+* MvPowerSeries (Fin n) K where
  toFun := face k
  map_one' := face_one k
  map_mul' := face_mul k
  map_zero' := face_zero k
  map_add' := face_add k

lemma coeff_faceHom (k : ℕ) (f : MvPowerSeries (Fin n) K) (β : Fin n →₀ ℕ) :
    coeff β (faceHom k f) = if ∀ i : Fin n, (i : ℕ) < k → β i = 0 then coeff β f else 0 := rfl

end Face

section Prime

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma Chart.RF_indW (c : Chart R n) (k : ℕ) :
    c.RF (indW k) 1 = Ideal.span (c.x '' {i | (i : ℕ) < k}) := by
  classical
  apply le_antisymm
  · rw [Chart.RF, Ideal.span_le]
    rintro _ ⟨α, h0, hα, rfl⟩
    have : ∃ i : Fin n, (i : ℕ) < k ∧ α i ≠ 0 := by
      by_contra h; push Not at h
      have : lam (indW k) α < 1 := lam_indW_lt_one.2 fun i hi => h i hi
      linarith
    obtain ⟨i, hi, hne⟩ := this
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem c.x hi)) _
      (Nat.pos_of_ne_zero hne)
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Set.mem_ofPred_eq] at hi
    apply Ideal.subset_span
    refine ⟨Finsupp.single i 1, fun j hj => ?_, ?_, ?_⟩
    · by_contra hne
      have : j = i := by
        by_contra hji; exact hne (by simp [Ne.symm hji])
      subst this
      simp only [indW, ite_eq_left hi] at hj
      norm_num at hj
    · rw [lam_single]; simp [indW, hi]
    · rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp

lemma Chart.IsCentred.mem_span_x_iff (c : Chart R n) (hc : c.IsCentred) (k : ℕ) (f : R) :
    f ∈ Ideal.span (c.x '' {i | (i : ℕ) < k}) ↔ faceHom k (c.tau f) = 0 := by
  rw [← c.RF_indW k, hc.mem_RF_iff (indW_nonneg k)]
  constructor
  · intro h
    ext β
    rw [coeff_faceHom, map_zero]
    split_ifs with hβ
    · exact h β (lam_indW_lt_one.2 hβ)
    · rfl
  · intro h β hβ
    have := congrArg (coeff β) h
    rw [coeff_faceHom, ite_eq_left (lam_indW_lt_one.1 hβ), map_zero] at this
    exact this

/-- **Quotients by initial coordinates of a centred chart are domains**: `(x₀, …, x_{k-1})` is
prime. -/
theorem Chart.IsCentred.span_x_isPrime (c : Chart R n) (hc : c.IsCentred) (k : ℕ)
    [IsDomain (ResidueField R)] : (Ideal.span (c.x '' {i | (i : ℕ) < k})).IsPrime := by
  refine ⟨fun htop => ?_, fun {f g} hfg => ?_⟩
  · have h1 : (1 : R) ∈ Ideal.span (c.x '' {i | (i : ℕ) < k}) := by rw [htop]; trivial
    rw [hc.mem_span_x_iff] at h1
    have := congrArg (coeff 0) h1
    have h0 : ∀ i : Fin n, (i : ℕ) < k → (0 : Fin n →₀ ℕ) i = 0 := fun _ _ => rfl
    rw [coeff_faceHom, ite_eq_left h0, map_one, map_zero, coeff_one, ite_eq_left rfl] at this
    exact one_ne_zero this
  · rw [hc.mem_span_x_iff, map_mul, map_mul] at hfg
    rcases mul_eq_zero.1 hfg with h | h
    · left; rwa [hc.mem_span_x_iff]
    · right; rwa [hc.mem_span_x_iff]

end Prime

end BezoutCounterexample.Principalization

