import BezoutCounterexample.Principalization.TorsorInv

/-!
# Vertical derivations and chart sizes on the torsor (the length bound)

Lemma 4.4 (`lem:length-control`) of the paper, and the consequence `δ(𝓕_j) ⊆ 𝓕_j` of
Lemma 3.7 (1).

* `lder`, `eulerL`: coefficientwise and Euler derivations of Laurent polynomials; `reesLift`,
  `reesEuler` on the Rees algebra; `deriv_mem_compF`: derivations stabilizing `I` stabilize the
  component filtration.
* `jLift`, `jEuler`, `jTheta`: derivations of the Jouanolou torsor; `det_fam`.
* `VertOK`, `DimOK`, `invAt_eq_zero_of_ok`: the length bound; `torsor_vertOK`, `torsor_dimOK`:
  both conditions pass to the torsor with `m ↦ m + nGen + 1`.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section LDer

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- The coefficientwise linear map. -/
def lderLin (δ : Derivation ℚ B B) : B[T;T⁻¹] →ₗ[ℚ] B[T;T⁻¹] :=
  (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap δ.toLinearMap ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

lemma lderLin_single (δ : Derivation ℚ B B) (n : ℤ) (a : B) :
    lderLin δ (AddMonoidAlgebra.single n a) = AddMonoidAlgebra.single n (δ a) := by
  show AddMonoidAlgebra.ofCoeff (Finsupp.mapRange δ δ.map_zero (Finsupp.single n a)) = _
  rw [Finsupp.mapRange_single]; rfl

lemma lderLin_coeff (δ : Derivation ℚ B B) (p : B[T;T⁻¹]) (j : ℤ) :
    (lderLin δ p).coeff j = δ (p.coeff j) := rfl

end LDer

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section LDer2

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- The coefficientwise extension of a derivation to Laurent polynomials. -/
def lder (δ : Derivation ℚ B B) : Derivation ℚ B[T;T⁻¹] B[T;T⁻¹] := by
  refine Derivation.mk' (lderLin δ) ?_
  intro p q
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_mul, map_add, hp, hp', map_add, smul_add, add_smul]; abel
  | single n a =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add q q' hq hq' => rw [mul_add, map_add, hq, hq', map_add, smul_add, add_smul]; abel
    | single m b =>
      rw [AddMonoidAlgebra.single_mul_single, lderLin_single, lderLin_single, lderLin_single,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, add_comm m n,
        ← AddMonoidAlgebra.single_add]

lemma lder_coeff (δ : Derivation ℚ B B) (p : B[T;T⁻¹]) (j : ℤ) :
    (lder δ p).coeff j = δ (p.coeff j) := rfl

lemma lder_C_mul_T (δ : Derivation ℚ B B) (a : B) (j : ℤ) :
    lder δ (LaurentPolynomial.C a * T j) = LaurentPolynomial.C (δ a) * T j := by
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T]
  exact lderLin_single δ j a

end LDer2

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section Euler

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- The Euler linear map `∑ aⱼ Tʲ ↦ ∑ j aⱼ Tʲ`. -/
def eulerLin : B[T;T⁻¹] →ₗ[ℚ] B[T;T⁻¹] :=
  (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ
    (Finsupp.lsum ℚ fun n : ℤ => Finsupp.lsingle n ∘ₗ (n • LinearMap.id : B →ₗ[ℚ] B)) ∘ₗ
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

lemma eulerLin_single (n : ℤ) (a : B) :
    eulerLin (AddMonoidAlgebra.single n a) = AddMonoidAlgebra.single n (n • a) := by
  show AddMonoidAlgebra.ofCoeff ((Finsupp.lsum ℚ fun n : ℤ => Finsupp.lsingle n ∘ₗ
    (n • LinearMap.id : B →ₗ[ℚ] B)) (Finsupp.single n a)) = _
  rw [Finsupp.lsum_single]; rfl

/-- **The Euler derivation** `T d/dT`. -/
def eulerL : Derivation ℚ B[T;T⁻¹] B[T;T⁻¹] := by
  refine Derivation.mk' (eulerLin (B := B)) ?_
  intro p q
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [add_mul, map_add, hp, hp', map_add, smul_add, add_smul]; abel
  | single n a =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add q q' hq hq' => rw [mul_add, map_add, hq, hq', map_add, smul_add, add_smul]; abel
    | single m b =>
      rw [AddMonoidAlgebra.single_mul_single, eulerLin_single, eulerLin_single, eulerLin_single,
        smul_eq_mul, smul_eq_mul, AddMonoidAlgebra.single_mul_single,
        AddMonoidAlgebra.single_mul_single, add_comm m n, ← AddMonoidAlgebra.single_add]
      congr 1
      rw [add_smul, mul_smul_comm, mul_smul_comm, mul_comm b a, add_comm]

lemma eulerL_C_mul_T (a : B) (j : ℤ) :
    eulerL (LaurentPolynomial.C a * T j) = LaurentPolynomial.C (j • a) * T j := by
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T]
  exact eulerLin_single j a

lemma eulerL_coeff (p : B[T;T⁻¹]) (j : ℤ) : (eulerL p).coeff j = j • p.coeff j := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, smul_add]
  | single n a =>
    show (eulerLin (AddMonoidAlgebra.single n a)).coeff j = _
    rw [eulerLin_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · rw [smul_zero]

end Euler

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

section DerStable

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- A derivation mapping the generators of an ideal into it stabilizes the ideal. -/
lemma deriv_mem_span (D : Derivation ℚ S S) {G : Set S} (hG : ∀ g ∈ G, D g ∈ Ideal.span G)
    {f : S} (hf : f ∈ Ideal.span G) : D f ∈ Ideal.span G := by
  induction hf using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x hx ihx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ ihx) (Ideal.mul_mem_right _ _ hx)

/-- A derivation stabilizes an extended ideal if it stabilizes the original one. -/
lemma deriv_mem_map {R : Type*} [CommRing R] [Algebra ℚ R] (φ : R →+* S) (D : Derivation ℚ S S)
    (D₀ : Derivation ℚ R R) (hD : ∀ r, D (φ r) = φ (D₀ r)) {J : Ideal R}
    (hJ : ∀ f ∈ J, D₀ f ∈ J) {f : S} (hf : f ∈ J.map φ) : D f ∈ J.map φ := by
  refine deriv_mem_span D (fun g hg => ?_) hf
  obtain ⟨r, hr, rfl⟩ := hg
  rw [hD]
  exact Ideal.mem_map_of_mem _ (hJ r hr)

variable {n : ℕ} (c : Chart S n)

lemma monom_mem_RF {e : Fin n → ℚ} {α : Fin n →₀ ℕ} (h0 : ∀ i, e i = 0 → α i = 0) :
    ∏ i, c.x i ^ α i ∈ c.RF e (lam e α) :=
  Ideal.subset_span ⟨α, h0, le_rfl, rfl⟩

lemma deriv_monom_mem_RF {e : Fin n → ℚ} (D : Derivation ℚ S S)
    (hD : ∀ i, e i ≠ 0 → D (c.x i) ∈ c.RF e (e i)) (α : Fin n →₀ ℕ) :
    (∀ i, e i = 0 → α i = 0) → D (∏ i, c.x i ^ α i) ∈ c.RF e (lam e α) := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => intro _; simp
  | add α β hα hβ =>
    intro h0
    have h0α : ∀ i, e i = 0 → α i = 0 := fun i hi => by
      have := h0 i hi; rw [Finsupp.add_apply] at this; omega
    have h0β : ∀ i, e i = 0 → β i = 0 := fun i hi => by
      have := h0 i hi; rw [Finsupp.add_apply] at this; omega
    have hprod : ∏ i, c.x i ^ (α + β) i = (∏ i, c.x i ^ α i) * ∏ i, c.x i ^ β i := by
      simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [hprod, Derivation.leibniz, smul_eq_mul, smul_eq_mul, lam_add]
    refine add_mem ?_ ?_
    · have := c.RF_mul_le e (lam e α) (lam e β)
      exact this (Ideal.mul_mem_mul (monom_mem_RF c h0α) (hβ h0β))
    · have := c.RF_mul_le e (lam e β) (lam e α)
      rw [add_comm]
      exact this (Ideal.mul_mem_mul (monom_mem_RF c h0β) (hα h0α))
  | single i k =>
    intro h0
    have hprod : ∏ j, c.x j ^ (Finsupp.single i k) j = c.x i ^ k := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro l _ hl; rw [Finsupp.single_apply, if_neg (Ne.symm hl), pow_zero]
      · simp
    rw [hprod, lam_single]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hei : e i ≠ 0 := fun h => by
      have := h0 i h; rw [Finsupp.single_eq_same] at this; omega
    rw [Derivation.leibniz_pow]
    have h1 : c.x i ^ (k - 1) ∈ c.RF e ((k - 1 : ℕ) * e i) := by
      have := monom_mem_RF c (e := e) (α := Finsupp.single i (k - 1)) (fun j hj => by
        rw [Finsupp.single_apply]; split_ifs with h
        · subst h; exact absurd hj hei
        · rfl)
      rw [lam_single] at this
      have hprod' : ∏ j, c.x j ^ (Finsupp.single i (k - 1)) j = c.x i ^ (k - 1) := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro l _ hl; rw [Finsupp.single_apply, if_neg (Ne.symm hl), pow_zero]
        · simp
      rwa [hprod'] at this
    have h2 := c.RF_mul_le e ((k - 1 : ℕ) * e i) (e i) (Ideal.mul_mem_mul h1 (hD i hei))
    have hk' : ((k - 1 : ℕ) : ℚ) * e i + e i = (k : ℚ) * e i := by
      have : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
        rw [Nat.cast_sub hk]; simp
      rw [this]; ring
    rw [hk'] at h2
    simp only [smul_eq_mul, nsmul_eq_mul]
    exact Ideal.mul_mem_left _ _ h2

/-- **Derivation-stability of weighted monomial ideals.** -/
theorem deriv_mem_RF_of_x {e : Fin n → ℚ} (D : Derivation ℚ S S)
    (hD : ∀ i, e i ≠ 0 → D (c.x i) ∈ c.RF e (e i)) (t : ℚ) {f : S} (hf : f ∈ c.RF e t) :
    D f ∈ c.RF e t := by
  refine deriv_mem_span D (fun g hg => ?_) hf
  obtain ⟨α, h0, ht, rfl⟩ := hg
  exact c.RF_antitone e ht (deriv_monom_mem_RF c D hD α h0)

end DerStable

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

section CompFDer

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)

include hI hmax h𝔭 in
/-- **Derivations stabilizing `I` stabilize the component filtration.** -/
theorem deriv_mem_compF (δ : Derivation ℚ A A) (hδ : ∀ f ∈ I, δ f ∈ I) (t : ℚ) {f : A}
    (hf : f ∈ compF I 𝔭 t) : δ f ∈ compF I 𝔭 t := by
  rw [mem_compF] at hf ⊢
  intro 𝔪 _ h𝔭𝔪
  obtain ⟨hI𝔪, n, e, he, -⟩ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
  haveI : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl _ inferInstance
  obtain ⟨J, -, -⟩ := he.1
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ :=
    he.exists_run (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred
  set δ𝔪 : Derivation ℚ (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪) :=
    extLoc (S := Localization.AtPrime 𝔪) 𝔪.primeCompl δ
  have hδ𝔪 : ∀ g ∈ Iloc I 𝔪, δ𝔪 g ∈ Iloc I 𝔪 := fun g hg =>
    deriv_mem_map (algebraMap A _) δ𝔪 δ (fun r => extLoc_algebraMap _ δ r) hδ hg
  have hx : ∀ i, e i ≠ 0 → δ𝔪 (ck.x i) ∈ ck.RF e (e i) := fun i hi =>
    deriv_mem_RF hrun hadm hck he.nonneg he.anti hsupp δ𝔪 hδ𝔪 i ((hsupp i).1 hi)
  have hcRF : cRF I 𝔪 t = ck.RF e t :=
    cRF_eq hI hI𝔪 (J := ⟨ck, e, hck, he.nonneg, he.anti⟩) hadm he t
  have h1 := hf 𝔪 h𝔭𝔪
  rw [hcRF] at h1 ⊢
  rw [← extLoc_algebraMap 𝔪.primeCompl δ f]
  exact deriv_mem_RF_of_x ck δ𝔪 hx t h1

end CompFDer

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section ReesDer

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B)

/-- Restriction of a derivation of `B[T^±]` preserving the Rees algebra. -/
def reesRestr (D : Derivation ℚ B[T;T⁻¹] B[T;T⁻¹]) (hD : ∀ p ∈ ReesAlg Φ, D p ∈ ReesAlg Φ) :
    Derivation ℚ (ReesAlg Φ) (ReesAlg Φ) where
  toFun p := ⟨D (p : B[T;T⁻¹]), hD _ p.2⟩
  map_add' p q := Subtype.ext (map_add D (p : B[T;T⁻¹]) q)
  map_smul' q p := Subtype.ext (by
    show D (q • (p : B[T;T⁻¹])) = q • D (p : B[T;T⁻¹])
    exact D.map_smul q _)
  map_one_eq_zero' := Subtype.ext D.map_one_eq_zero
  leibniz' p q := Subtype.ext (D.leibniz (p : B[T;T⁻¹]) q)

lemma reesRestr_coe (D : Derivation ℚ B[T;T⁻¹] B[T;T⁻¹]) (hD) (p : ReesAlg Φ) :
    (reesRestr Φ D hD p : B[T;T⁻¹]) = D p := rfl

/-- The lift `∑ fⱼ Tʲ ↦ ∑ δ(fⱼ) Tʲ` of a derivation stabilizing the filtration. -/
def reesLift (δ : Derivation ℚ B B) (hδ : ∀ j, ∀ f ∈ Φ.F j, δ f ∈ Φ.F j) :
    Derivation ℚ (ReesAlg Φ) (ReesAlg Φ) :=
  reesRestr Φ (lder δ) (fun p hp j => by rw [lder_coeff]; exact hδ j _ (hp j))

/-- The Euler derivation of the Rees algebra. -/
def reesEuler : Derivation ℚ (ReesAlg Φ) (ReesAlg Φ) :=
  reesRestr Φ eulerL (fun p hp j => by rw [eulerL_coeff]; exact Submodule.smul_of_tower_mem _ j (hp j))

lemma reesLift_algebraMap (δ : Derivation ℚ B B) (hδ) (b : B) :
    reesLift Φ δ hδ (algebraMap B (ReesAlg Φ) b) = algebraMap B (ReesAlg Φ) (δ b) := by
  apply Subtype.ext
  show lder δ (algebraMap B B[T;T⁻¹] b) = algebraMap B B[T;T⁻¹] (δ b)
  have := lder_C_mul_T δ b 0
  rw [T_zero, mul_one, mul_one] at this
  rw [← LaurentPolynomial.C_eq_algebraMap, ← LaurentPolynomial.C_eq_algebraMap, this]

lemma reesLift_C_mul_T (δ : Derivation ℚ B B) (hδ) {j : ℤ} {f : B} (hf : f ∈ Φ.F j) :
    reesLift Φ δ hδ ⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ =
      ⟨LaurentPolynomial.C (δ f) * T j, C_mul_T_mem_ReesAlg (hδ j f hf)⟩ :=
  Subtype.ext (lder_C_mul_T δ f j)

lemma reesEuler_algebraMap (b : B) : reesEuler Φ (algebraMap B (ReesAlg Φ) b) = 0 := by
  apply Subtype.ext
  show eulerL (algebraMap B B[T;T⁻¹] b) = 0
  have := eulerL_C_mul_T (B := B) b 0
  rw [T_zero, mul_one, mul_one, zero_smul, map_zero] at this
  rw [← LaurentPolynomial.C_eq_algebraMap, this]

lemma reesEuler_C_mul_T {j : ℤ} {f : B} (hf : f ∈ Φ.F j) :
    reesEuler Φ ⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ =
      j • (⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ : ReesAlg Φ) := by
  apply Subtype.ext
  show eulerL (LaurentPolynomial.C f * T j) = j • (LaurentPolynomial.C f * T j)
  rw [eulerL_C_mul_T, map_zsmul, smul_mul_assoc]

lemma reesLift_weakT (δ : Derivation ℚ B B) (hδ) {I : Ideal B} (hδI : ∀ f ∈ I, δ f ∈ I) (d : ℤ)
    (hId : I ≤ Φ.F d) {p : ReesAlg Φ} (hp : p ∈ weakT Φ I d hId) :
    reesLift Φ δ hδ p ∈ weakT Φ I d hId := by
  refine deriv_mem_span _ (fun g hg => ?_) hp
  obtain ⟨f, rfl⟩ := hg
  rw [reesLift_C_mul_T Φ δ hδ (hId f.2)]
  exact Ideal.subset_span ⟨⟨δ f, hδI f f.2⟩, rfl⟩

lemma reesEuler_weakT {I : Ideal B} (d : ℤ) (hId : I ≤ Φ.F d) {p : ReesAlg Φ}
    (hp : p ∈ weakT Φ I d hId) : reesEuler Φ p ∈ weakT Φ I d hId := by
  refine deriv_mem_span _ (fun g hg => ?_) hp
  obtain ⟨f, rfl⟩ := hg
  rw [reesEuler_C_mul_T Φ (hId f.2)]
  exact Submodule.smul_of_tower_mem _ d (Ideal.subset_span ⟨f, rfl⟩)

end ReesDer

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open Jou

section TorsorDer

variable {R : Type*} [CommRing R] [Algebra ℚ R] {r : ℕ} (y : Fin (r + 1) → R)

/-- The lift of a derivation of `R` to `J(y)`, with `σᵢ ↦ -σᵢ ∑ σₗ D(yₗ)`. -/
def jLift (D : Derivation ℚ R R) : Derivation ℚ (J y) (J y) :=
  Jou.liftDer D (fun i => -(σ y i * ∑ l, σ y l * algebraMap R (J y) (D (y l)))) (by
    have h1 := Jou.sum_σ_mul y
    rw [Finset.sum_add_distrib]
    have : ∑ i, algebraMap R (J y) (y i) * -(σ y i * ∑ l, σ y l * algebraMap R (J y) (D (y l))) =
        -((∑ i, σ y i * algebraMap R (J y) (y i)) * ∑ l, σ y l * algebraMap R (J y) (D (y l))) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h1, one_mul, add_neg_cancel])

lemma jLift_algebraMap (D : Derivation ℚ R R) (a : R) :
    jLift y D (algebraMap R (J y) a) = algebraMap R (J y) (D a) :=
  Jou.liftDer_algebraMap _ _ _ a

/-- The lift of an Euler-type derivation (`D yᵢ = wᵢ yᵢ`) with `σᵢ ↦ -wᵢ σᵢ`. -/
def jEuler (D : Derivation ℚ R R) (w : Fin (r + 1) → ℤ) (hD : ∀ i, D (y i) = w i • y i) :
    Derivation ℚ (J y) (J y) :=
  Jou.liftDer D (fun i => -(w i • σ y i)) (by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hD, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
    ring)

lemma jEuler_algebraMap (D : Derivation ℚ R R) (w : Fin (r + 1) → ℤ) (hD) (a : R) :
    jEuler y D w hD (algebraMap R (J y) a) = algebraMap R (J y) (D a) :=
  Jou.liftDer_algebraMap _ _ _ a

lemma jEuler_σ (D : Derivation ℚ R R) (w : Fin (r + 1) → ℤ) (hD) (i : Fin (r + 1)) :
    jEuler y D w hD (σ y i) = -(w i • σ y i) :=
  Jou.liftDer_σ _ _ _ i

/-- The values of the vertical derivation `θ_{l,b} = y_{b'} ∂/∂σ_l - y_l ∂/∂σ_{b'}`. -/
def thetaV (l : Fin (r + 1)) (b : Fin r) (i : Fin (r + 1)) : J y :=
  if i = l then algebraMap R (J y) (y (l.succAbove b))
  else if i = l.succAbove b then -algebraMap R (J y) (y l) else 0

/-- The vertical derivation `θ_{l,b}`. -/
def jTheta (l : Fin (r + 1)) (b : Fin r) : Derivation ℚ (J y) (J y) :=
  Jou.liftDer 0 (thetaV y l b) (by
    simp only [Derivation.zero_apply, map_zero, mul_zero, zero_add]
    rw [Fintype.sum_eq_add l (l.succAbove b) (Fin.succAbove_ne l b).symm (fun i hi => by
      simp [thetaV, hi.1, hi.2])]
    simp only [thetaV, if_pos rfl, if_neg (Fin.succAbove_ne l b), ite_true]
    ring)

lemma jTheta_algebraMap (l : Fin (r + 1)) (b : Fin r) (a : R) :
    jTheta y l b (algebraMap R (J y) a) = 0 := by
  rw [jTheta, Jou.liftDer_algebraMap]; simp

lemma jTheta_σ (l : Fin (r + 1)) (b : Fin r) (i : Fin (r + 1)) :
    jTheta y l b (σ y i) = thetaV y l b i :=
  Jou.liftDer_σ _ _ _ i

end TorsorDer

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

section LengthBound

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- Stabilizing derivations of `I`, independent at every point of `V(I)`. -/
def VertOK (I : Ideal A) (m : ℕ) : Prop :=
  ∀ (𝔪 : Ideal A), 𝔪.IsMaximal → I ≤ 𝔪 → ∃ (δ : Fin m → Derivation ℚ A A) (y : Fin m → A),
    (∀ j, ∀ f ∈ I, δ j f ∈ I) ∧ (Matrix.of fun j l => δ j (y l)).det ∉ 𝔪

/-- Chart sizes at points of `V(I)` are at most `N + m`. -/
def DimOK (I : Ideal A) (m N : ℕ) : Prop :=
  ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ n, Nonempty (Chart (Localization.AtPrime 𝔪) n) →
    n ≤ N + m

lemma det_extLoc (𝔪 : Ideal A) [𝔪.IsPrime] {m : ℕ} (δ : Fin m → Derivation ℚ A A) (y : Fin m → A) :
    (Matrix.of fun j l => extLoc (S := Localization.AtPrime 𝔪) 𝔪.primeCompl (δ j)
      (algebraMap A _ (y l))).det = algebraMap A _ (Matrix.of fun j l => δ j (y l)).det := by
  rw [RingHom.map_det]
  congr 1
  ext j l
  simp [extLoc_algebraMap]

variable [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A]

/-- **The length bound**: under `VertOK` and `DimOK`, invariants are supported below `N`. -/
theorem invAt_eq_zero_of_ok {I : Ideal A} (hI : I ≠ ⊥) {m N : ℕ} (hV : VertOK I m)
    (hD : DimOK I m N) (𝔪 : Ideal A) [h𝔪 : 𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) {v : ℕ → ℚ}
    (hv : InvAt I 𝔪 v) (i : ℕ) (hi : N ≤ i) : v i = 0 := by
  obtain ⟨n, e, he, rfl⟩ := hv
  haveI : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl _ inferInstance
  obtain ⟨J, -, -⟩ := he.1
  have hn : n ≤ N + m := hD 𝔪 hI𝔪 n ⟨J.c⟩
  obtain ⟨δ, y, hδ, hdet⟩ := hV 𝔪 h𝔪 hI𝔪
  by_cases hin : i < n
  · simp only [ext0, dif_pos hin]
    refine IsInv.eq_zero_of_derivations (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) he J.c J.centred
      (fun j => extLoc (S := Localization.AtPrime 𝔪) 𝔪.primeCompl (δ j))
      (fun j f hf => deriv_mem_map (algebraMap A _) _ (δ j) (fun r => extLoc_algebraMap _ _ r)
        (hδ j) hf)
      (fun l => algebraMap A _ (y l)) ?_ ⟨i, hin⟩ (by simp; omega)
    rw [det_extLoc]
    exact IsLocalization.map_units (Localization.AtPrime 𝔪) (⟨_, hdet⟩ : 𝔪.primeCompl)
  · simp only [ext0, dif_neg hin]

end LengthBound

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

section ChartSize

/-- **Chart sizes are constant on a domain.** -/
lemma chart_card_eq_of_domain {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] (𝔭 𝔮 : Ideal B)
    [𝔭.IsPrime] [𝔮.IsPrime] {n n' : ℕ} (c : Chart (Localization.AtPrime 𝔭) n)
    (c' : Chart (Localization.AtPrime 𝔮) n') : n = n' :=
  Chart.card_eq (Loc.transport (Ideal.primeCompl_le_nonZeroDivisors 𝔭) c)
    (Loc.transport (Ideal.primeCompl_le_nonZeroDivisors 𝔮) c')

lemma exists_chart_atPrime {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]
    (p : Ideal B) [p.IsPrime] : ∃ n, Nonempty (Chart (Localization.AtPrime p) n) := by
  obtain ⟨f, hf, n, ⟨c⟩⟩ := exists_chart_away p
  have h : Submonoid.powers f ≤ p.primeCompl := (Submonoid.powers_le).2 hf
  exact ⟨n, ⟨Loc.transport h c⟩⟩

/-- Chart sizes on the Rees algebra are one more than on the base. -/
theorem rees_chart_card {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] (Φ : WFil B)
    (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤) (𝔪 : Ideal B) [𝔪.IsPrime] {nA : ℕ}
    (cA : Chart (Localization.AtPrime 𝔪) nA) (P : Ideal (ReesAlg Φ)) [P.IsPrime] {n : ℕ}
    (c : Chart (Localization.AtPrime P) n) : n = nA + 1 := by
  haveI : (⊥ : Ideal (ReesAlg Φ)).IsPrime := Ideal.isPrime_bot
  have hs0 : reesS Φ hneg ∉ (⊥ : Ideal (ReesAlg Φ)) := by
    rw [Ideal.mem_bot]
    intro h
    have := congrArg (fun p : ReesAlg Φ => (p : B[T;T⁻¹])) h
    simp only [reesS_coe, ZeroMemClass.coe_zero] at this
    exact (isUnit_T (-1 : ℤ)).ne_zero this
  have h𝔮₀ : (⊥ : Ideal (ReesAlg Φ)).comap (algebraMap B (ReesAlg Φ)) ≤ 𝔪 := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := rees_algebraMap_injective Φ (hx.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  have hle : 𝔪.primeCompl ≤ ((⊥ : Ideal (ReesAlg Φ)).comap (algebraMap B (ReesAlg Φ))).primeCompl :=
    fun x hx h => hx (h𝔮₀ h)
  obtain ⟨c0⟩ := chart_of_polyLoc
    (S := Localization.AtPrime ((⊥ : Ideal (ReesAlg Φ)).comap (algebraMap B (ReesAlg Φ))))
    (S' := Localization.AtPrime (⊥ : Ideal (ReesAlg Φ))) (theta1 Φ hneg ⊥ hs0 _ rfl) (theta1_injective Φ hneg ⊥ hs0 _ rfl)
    (theta1_surj Φ hneg ⊥ hs0 _ rfl) (Loc.transport hle cA)
  exact chart_card_eq_of_domain P ⊥ c c0

end ChartSize

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open Jou

section DetGeneric

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra ℚ A] [Algebra ℚ R] [Algebra A R]
  [IsScalarTower ℚ A R] {r m : ℕ} (y : Fin (r + 1) → R)
  (DR : Fin m → Derivation ℚ R R) (E : Derivation ℚ R R) (w : Fin (r + 1) → ℤ)
  (hE : ∀ i, E (y i) = w i • y i) (l : Fin (r + 1)) (yA : Fin m → A)

/-- The derivations on the torsor: lifts, Euler, vertical. -/
def famD : Fin m ⊕ Fin (r + 1) → Derivation ℚ (J y) (J y) :=
  Sum.elim (fun j => jLift y (DR j)) (Fin.cons (jEuler y E w hE) (fun b => jTheta y l b))

/-- The test functions on the torsor. -/
def famY : Fin m ⊕ Fin (r + 1) → J y :=
  Sum.elim (fun j => algebraMap A (J y) (yA j))
    (Fin.cons (algebraMap R (J y) (y l)) (fun b => σ y (l.succAbove b)))

theorem det_fam (δ : Fin m → Derivation ℚ A A)
    (hDR : ∀ j a, DR j (algebraMap A R a) = algebraMap A R (δ j a))
    (hEA : ∀ a, E (algebraMap A R a) = 0) :
    (Matrix.of fun i i' => famD y DR E w hE l i (famY y l yA i')).det =
      algebraMap A (J y) (Matrix.of fun j j' => δ j (yA j')).det *
        (algebraMap R (J y) (w l • y l) * (-algebraMap R (J y) (y l)) ^ r) := by
  classical
  set M := Matrix.of fun i i' => famD y DR E w hE l i (famY y l yA i')
  have hAU : ∀ a : A, algebraMap A (J y) a = algebraMap R (J y) (algebraMap A R a) :=
    fun a => IsScalarTower.algebraMap_apply A R (J y) a
  have h21 : M.toBlocks₂₁ = 0 := by
    ext a j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, M, famD, famY, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_apply]
    rw [hAU]
    cases a using Fin.cases with
    | zero => rw [Fin.cons_zero, jEuler_algebraMap, hEA, map_zero]
    | succ b => rw [Fin.cons_succ, jTheta_algebraMap]
  have h11 : M.toBlocks₁₁ = (algebraMap A (J y)).mapMatrix (Matrix.of fun j j' => δ j (yA j')) := by
    ext j j'
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, M, famD, famY, Sum.elim_inl,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hAU, jLift_algebraMap, hDR, ← hAU]
  have htri : M.toBlocks₂₂.BlockTriangular id := by
    intro a a' h
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, M, famD, famY, Sum.elim_inr, id] at h ⊢
    cases a using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero _)
    | succ b =>
      rw [Fin.cons_succ]
      cases a' using Fin.cases with
      | zero => rw [Fin.cons_zero, jTheta_algebraMap]
      | succ c =>
        rw [Fin.cons_succ, jTheta_σ, thetaV, if_neg (Fin.succAbove_ne l c), if_neg]
        intro hc
        have := (Fin.succAbove_right_inj).1 hc
        subst this
        exact lt_irrefl _ h
  have hdiag : ∏ a, M.toBlocks₂₂ a a =
      algebraMap R (J y) (w l • y l) * (-algebraMap R (J y) (y l)) ^ r := by
    rw [Fin.prod_univ_succ]
    congr 1
    · simp only [Matrix.toBlocks₂₂, Matrix.of_apply, M, famD, famY, Sum.elim_inr, Fin.cons_zero]
      rw [jEuler_algebraMap, hE]
    · rw [← Fin.prod_const]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Matrix.toBlocks₂₂, Matrix.of_apply, M, famD, famY, Sum.elim_inr, Fin.cons_succ]
      rw [jTheta_σ, thetaV, if_neg (Fin.succAbove_ne l b), if_pos rfl]
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h11, ← RingHom.map_det,
    Matrix.det_of_upperTriangular htri, hdiag]

end DetGeneric

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial Jou

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

include hd in
lemma le_comap_of_torsorI (Q : Ideal (Torsor hI hmax h𝔭 d hπ))
    (hIQ : torsorI hI hmax h𝔭 hd hπ ≤ Q) : I ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  rw [← Ideal.map_le_iff_le_comap, torsor_map_eq hI hmax h𝔭 hd hπ]
  exact Ideal.mul_le_right.trans hIQ

include hd hw hπ0 in
/-- **Chart sizes on the torsor.** -/
theorem torsor_dimOK {m N : ℕ} (hD : DimOK I m N) :
    DimOK (torsorI hI hmax h𝔭 hd hπ) (m + (nGen hI hmax h𝔭 d + 1)) N := by
  intro Q _ hIQ n ⟨c⟩
  haveI : Algebra.FiniteType A (ReesAlg (compFil hI hmax h𝔭 d)) :=
    reesAlg_finiteType hI hmax h𝔭 d hd hw
  haveI : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : Algebra.Smooth ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := rees_smooth hI hmax h𝔭 hd hw
  haveI : IsDomain (Torsor hI hmax h𝔭 d hπ) := torsor_isDomain hI hmax h𝔭 hπ hπ0
  haveI : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have hI𝔪 := le_comap_of_torsorI hI hmax h𝔭 hd hπ Q hIQ
  haveI : (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
    comap_isMaximal_of_finiteType Q
  obtain ⟨nA, ⟨cA⟩⟩ := exists_chart_atPrime (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)))
  have hnA : nA ≤ N + m := hD _ hI𝔪 nA ⟨cA⟩
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem hI hmax h𝔭 hd hw hπ Q
  obtain ⟨nP, ⟨cP⟩⟩ := exists_chart_atPrime
    (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)))
  have hnP : nP = nA + 1 := rees_chart_card _ (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) _ cA _ cP
  obtain ⟨cU⟩ := chart_of_mvLoc
    (S := Localization.AtPrime (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
      (Torsor hI hmax h𝔭 d hπ))))
    (S' := Localization.AtPrime Q) (theta2 (torsorY hI hmax h𝔭 d hπ) Q hl)
    (theta2_injective _ Q hl) (theta2_surj _ Q hl) cP
  have hn : n = nP + nGen hI hmax h𝔭 d := Chart.card_eq c cU
  omega

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial Jou

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

lemma torsorY_euler (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    reesEuler (compFil hI hmax h𝔭 d) (torsorY hI hmax h𝔭 d hπ i) =
      genDeg hI hmax h𝔭 d i • torsorY hI hmax h𝔭 d hπ i :=
  reesEuler_C_mul_T _ (genCoeff_mem hI hmax h𝔭 d hπ i)

include hd hw hπ0 in
set_option maxHeartbeats 2000000 in
/-- **Vertical derivations on the torsor.** -/
theorem torsor_vertOK {m : ℕ} (hV : VertOK I m) :
    VertOK (torsorI hI hmax h𝔭 hd hπ) (m + (nGen hI hmax h𝔭 d + 1)) := by
  classical
  intro Q hQ hIQ
  haveI : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have hI𝔪 := le_comap_of_torsorI hI hmax h𝔭 hd hπ Q hIQ
  haveI : (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
    comap_isMaximal_of_finiteType Q
  obtain ⟨δ, yA, hδ, hdet⟩ := hV _ inferInstance hI𝔪
  have hδF : ∀ j, ∀ i, ∀ f ∈ (compFil hI hmax h𝔭 d).F i, δ j f ∈ (compFil hI hmax h𝔭 d).F i :=
    fun j i f hf => by
      rw [compFil_F] at hf ⊢
      exact deriv_mem_compF hI hmax h𝔭 (δ j) (hδ j) _ hf
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem hI hmax h𝔭 hd hw hπ Q
  set y := torsorY hI hmax h𝔭 d hπ
  set DR : Fin m → Derivation ℚ (ReesAlg (compFil hI hmax h𝔭 d)) (ReesAlg (compFil hI hmax h𝔭 d)) :=
    fun j => reesLift _ (δ j) (hδF j)
  set E := reesEuler (compFil hI hmax h𝔭 d)
  have hE := torsorY_euler hI hmax h𝔭 hπ
  set e := (finSumFinEquiv (m := m) (n := nGen hI hmax h𝔭 d + 1)).symm
  refine ⟨famD y DR E _ hE l ∘ e, famY y l yA ∘ e, ?_, ?_⟩
  · intro i x hx
    simp only [Function.comp_apply]
    rcases e i with j | a
    · exact deriv_mem_map (algebraMap _ _) _ (DR j) (jLift_algebraMap y (DR j))
        (fun f hf => reesLift_weakT _ (δ j) (hδF j) (hδ j) _ _ hf) hx
    · cases a using Fin.cases with
      | zero =>
        exact deriv_mem_map (algebraMap _ _) _ E (jEuler_algebraMap y E _ hE)
          (fun f hf => reesEuler_weakT _ _ _ hf) hx
      | succ b =>
        exact deriv_mem_map (algebraMap _ _) _ 0 (fun f => by
            show jTheta y l b _ = _
            rw [jTheta_algebraMap, Derivation.zero_apply, map_zero])
          (fun f _ => by rw [Derivation.zero_apply]; exact zero_mem _) hx
  · have hsub : (Matrix.of fun j l' => (famD y DR E _ hE l ∘ e) j ((famY y l yA ∘ e) l')) =
        (Matrix.of fun i i' => famD y DR E _ hE l i (famY y l yA i')).submatrix e e := rfl
    rw [hsub, Matrix.det_submatrix_equiv_self,
      det_fam y DR E _ hE l yA δ (fun j a => reesLift_algebraMap _ (δ j) (hδF j) a)
        (fun a => reesEuler_algebraMap _ a)]
    intro hmem
    rcases hQ.isPrime.mem_or_mem hmem with h | h
    · exact hdet h
    rcases hQ.isPrime.mem_or_mem h with h | h
    · rw [map_zsmul, zsmul_eq_mul] at h
      rcases hQ.isPrime.mem_or_mem h with h | h
      · have hu : IsUnit ((genDeg hI hmax h𝔭 d l : ℤ) : Torsor hI hmax h𝔭 d hπ) := by
          have hne : ((genDeg hI hmax h𝔭 d l : ℤ) : ℚ) ≠ 0 := by
            have := genDeg_pos hI hmax h𝔭 d l
            exact_mod_cast (by omega : genDeg hI hmax h𝔭 d l ≠ 0)
          have := (isUnit_iff_ne_zero.2 hne).map (algebraMap ℚ (Torsor hI hmax h𝔭 d hπ))
          rwa [map_intCast] at this
        exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
      · exact hl h
    · exact hl (by
        have := hQ.isPrime.mem_of_pow_mem _ h
        rwa [neg_mem_iff] at this)

end BezoutCounterexample.Principalization

