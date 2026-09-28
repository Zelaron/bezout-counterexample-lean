import BezoutCounterexample.MarkedCenter

/-!
# Section 3.3: the weighted invariant (Theorem 3.3)

Let `A` be a smooth finitely generated `ℚ`-domain and `I ⊂ A` a nonzero ideal.

* `IsInvariant I 𝔪 v`: `v` is the lexicographically smallest weight vector of an admissible marked
  center for `I` at `𝔪`; `inv I 𝔪` is this vector (the *invariant* `inv_𝔪(I)`), and
  `maxCenter I 𝔪 t` is the common weighted ideal `F_t(𝔪)` of the admissible marked centers with
  this weight vector (the *maximal center*).
* `maxinv I`: the largest invariant for `⪯`; `components I`: the primes `𝔭₁, …, 𝔭ᵣ` whose zero
  sets are the components of the maximal locus; `numComponents I = c(I)`.
* `globalCenter I 𝔭 t`: the global center `F_t` retaining the component `V(𝔭)`.
* `Γ`: the set of weight vectors of Theorem 3.3(5).

**Theorem 3.3** (`thm:invariant`), quoted in the paper from Abramovich–Temkin–Włodarczyk and
Brais, is proved here from the engine `Principalization/` (Method-1 runs, uniqueness of the
maximal admissible centre, upper semicontinuity, …):

1. `isInvariant_inv`, `MarkedCenter.F_eq_maxCenter`, `inv_le_one`, `inv_zero_eq_one_div_ord`,
   `exists_inv_zero_eq`, `inv_zero_le_of_le_pow`; bundled as `theorem_3_3_1`.
2. `inv_map_eq_of_localization_polynomial` (smooth invariance, in the case where `B_𝔫` is a
   localization of a polynomial ring over `A_𝔪`, exactly as stated in the paper).
3. `theorem_3_3_3`: the maximal invariant and the components of the maximal locus.
4. `theorem_3_3_4`: the global center localizes to the maximal centers.
5. `inv_mem_Γ`, `Γ_wellFoundedOn`; `next_weight_form` is the computation in the justification of
   the enlargement of `Γ`.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-! ## The invariant and the maximal center at a point -/

/-- `v` is the *invariant* of `I` at `𝔪`: the weight vector of an admissible marked center for `I`
at `𝔪` which is lexicographically smallest among all admissible marked centers at `𝔪`. -/
def IsInvariant (I 𝔪 : Ideal A) [𝔪.IsPrime] (v : ℕ → ℚ) : Prop :=
  (∃ J : MarkedCenter 𝔪, J.IsAdmissible I ∧ J.weights = v) ∧
    ∀ J : MarkedCenter 𝔪, J.IsAdmissible I → toLex v ≤ toLex J.weights

open Classical in
/-- The invariant `inv_𝔪(I)` (Theorem 3.3(1); a junk value if it does not exist). -/
def inv (I 𝔪 : Ideal A) [𝔪.IsPrime] : ℕ → ℚ :=
  if h : ∃ v, IsInvariant I 𝔪 v then h.choose else 0

/-- The maximal center `F_t(𝔪)` of `I` at `𝔪`: the common weighted ideals of the admissible marked
centers whose weight vector is `inv_𝔪(I)` (Theorem 3.3(1)). -/
def maxCenter (I 𝔪 : Ideal A) [𝔪.IsPrime] (t : ℚ) : Ideal (Localization.AtPrime 𝔪) :=
  ⨅ (J : MarkedCenter 𝔪) (_ : J.IsAdmissible I) (_ : J.weights = inv I 𝔪), J.F t

/-! ### Relation to the engine -/

section Bridge

variable {I : Ideal A} {𝔪 : Ideal A} [𝔪.IsMaximal]

/-- Extension by zeros reflects the lexicographic order. -/
lemma toLex_ext0_le_iff {n : ℕ} {e e' : Fin n → ℚ} :
    toLex (ext0 e) ≤ toLex (ext0 e') ↔ toLex e ≤ toLex e' := by
  refine ⟨fun h => ?_, ext0_le⟩
  by_contra h'
  rw [not_le] at h'
  have h2 : ext0 e' = ext0 e := toLex.injective (le_antisymm (ext0_le h'.le) h)
  exact h'.ne (congrArg toLex (ext0_injective h2))

/-- An engine marked centre whose weights extend to the invariant realizes the invariant. -/
lemma isInv_of_invAt (hI : I ≠ ⊥) (hI𝔪 : I ≤ 𝔪) {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) {m : ℕ}
    (J : MC (Localization.AtPrime 𝔪) m) (hJv : ext0 J.e = v) :
    IsInv (Iloc I 𝔪) m J.e := by
  obtain ⟨e₁, he₁⟩ := exists_isInv (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred
  have h1 : ext0 e₁ = v := InvAt.unique ⟨m, e₁, he₁, rfl⟩ hv
  rwa [← ext0_injective (h1.trans hJv.symm)]

/-- The invariant of the paper is the engine's `InvAt`. -/
theorem isInvariant_iff_invAt (hI : I ≠ ⊥) (hI𝔪 : I ≤ 𝔪) {v : ℕ → ℚ} :
    IsInvariant I 𝔪 v ↔ InvAt I 𝔪 v := by
  constructor
  · rintro ⟨⟨J₀, hJ₀, rfl⟩, hmin⟩
    obtain ⟨J₀', -, he, hRF⟩ := J₀.exists_mc
    refine ⟨J₀.n, J₀.e, ⟨⟨J₀', ?_, he⟩, fun J' hJ' => ?_⟩, rfl⟩
    · show Iloc I 𝔪 ≤ J₀'.RF 1
      rw [hRF]
      exact hJ₀
    · have h := hmin (MarkedCenter.ofMC J') (by
        show Iloc I 𝔪 ≤ (MarkedCenter.ofMC J').F 1
        rw [MarkedCenter.ofMC_F]
        exact hJ')
      rw [MarkedCenter.ofMC_weights] at h
      exact (toLex_ext0_le_iff (e := J₀.e) (e' := J'.e)).1 h
  · rintro ⟨n, e, he, rfl⟩
    obtain ⟨⟨J, hJ, rfl⟩, hmin⟩ := he
    refine ⟨⟨MarkedCenter.ofMC J, ?_, rfl⟩, fun J' hJ' => ?_⟩
    · show Iloc I 𝔪 ≤ (MarkedCenter.ofMC J).F 1
      rw [MarkedCenter.ofMC_F]
      exact hJ
    · obtain ⟨J'', -, he'', hRF⟩ := J'.exists_mc
      obtain ⟨e₁, he₁⟩ := exists_isInv (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J''.c J''.centred
      have hv : ext0 e₁ = ext0 J.e :=
        InvAt.unique ⟨J'.n, e₁, he₁, rfl⟩ ⟨n, J.e, ⟨⟨J, hJ, rfl⟩, hmin⟩, rfl⟩
      have hadm : J''.Adm (Iloc I 𝔪) := by
        show Iloc I 𝔪 ≤ J''.RF 1
        rw [hRF]
        exact hJ'
      have h1 := he₁.2 J'' hadm
      rw [he''] at h1
      rw [← hv]
      exact ext0_le h1

theorem invAt_inv (hI : I ≠ ⊥) (hI𝔪 : I ≤ 𝔪) : InvAt I 𝔪 (inv I 𝔪) := by
  obtain ⟨v, hv⟩ := exists_invAt hI 𝔪 hI𝔪
  have h : ∃ v, IsInvariant I 𝔪 v := ⟨v, (isInvariant_iff_invAt hI hI𝔪).2 hv⟩
  rw [inv, dite_eq_left h]
  exact (isInvariant_iff_invAt hI hI𝔪).1 h.choose_spec

theorem inv_eq_of_invAt (hI : I ≠ ⊥) (hI𝔪 : I ≤ 𝔪) {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) :
    inv I 𝔪 = v :=
  (invAt_inv hI hI𝔪).unique hv

/-- The maximal center of the paper is the engine's `cRF`. -/
theorem maxCenter_eq_cRF (hI : I ≠ ⊥) (hI𝔪 : I ≤ 𝔪) (t : ℚ) : maxCenter I 𝔪 t = cRF I 𝔪 t := by
  obtain ⟨n, e, he, hev⟩ := invAt_inv hI hI𝔪
  obtain ⟨J₀, hJ₀, rfl⟩ := he.1
  apply le_antisymm
  · have hadm : (MarkedCenter.ofMC J₀).IsAdmissible I := by
      show Iloc I 𝔪 ≤ (MarkedCenter.ofMC J₀).F 1
      rw [MarkedCenter.ofMC_F]
      exact hJ₀
    have h1 : maxCenter I 𝔪 t ≤ (MarkedCenter.ofMC J₀).F t :=
      iInf_le_of_le (MarkedCenter.ofMC J₀) (iInf_le_of_le hadm
        (iInf_le_of_le ((MarkedCenter.ofMC_weights J₀).trans hev) le_rfl))
    rwa [MarkedCenter.ofMC_F, ← cRF_eq hI hI𝔪 hJ₀ he] at h1
  · refine le_iInf fun J => le_iInf fun hJ => le_iInf fun hw => ?_
    obtain ⟨J', -, he', hRF⟩ := J.exists_mc
    have hJ' : J'.Adm (Iloc I 𝔪) := by
      show Iloc I 𝔪 ≤ J'.RF 1
      rw [hRF]
      exact hJ
    have hJ'i : IsInv (Iloc I 𝔪) J.n J'.e :=
      isInv_of_invAt hI hI𝔪 (invAt_inv hI hI𝔪) J' (by rw [he']; exact hw)
    rw [cRF_eq hI hI𝔪 hJ' hJ'i, hRF]

end Bridge

/-! ### Theorem 3.3(1) -/

section Part1

variable {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪)
include hI hI𝔪

/-- **Theorem 3.3(1)**: there is an admissible marked center for `I` at `𝔪` whose weight vector
is lexicographically smallest among all admissible marked centers at `𝔪`. -/
theorem exists_isInvariant : ∃ v, IsInvariant I 𝔪 v := by
  exact ⟨inv I 𝔪, (isInvariant_iff_invAt hI hI𝔪).2 (invAt_inv hI hI𝔪)⟩

theorem isInvariant_inv : IsInvariant I 𝔪 (inv I 𝔪) := by
  have h := exists_isInvariant hI hI𝔪
  rw [inv, dite_eq_left h]
  exact h.choose_spec

/-- **Theorem 3.3(1)**: all admissible marked centers with weight vector `inv_𝔪(I)` have the same
weighted ideals, the maximal center `F_t(𝔪)`. -/
theorem MarkedCenter.F_eq_maxCenter (J : MarkedCenter 𝔪) (hJ : J.IsAdmissible I)
    (hw : J.weights = inv I 𝔪) (t : ℚ) : J.F t = maxCenter I 𝔪 t := by
  obtain ⟨J', -, he', hRF⟩ := J.exists_mc
  have hJ' : J'.Adm (Iloc I 𝔪) := by
    show Iloc I 𝔪 ≤ J'.RF 1
    rw [hRF]
    exact hJ
  have hJ'i : IsInv (Iloc I 𝔪) J.n J'.e :=
    isInv_of_invAt hI hI𝔪 (invAt_inv hI hI𝔪) J' (by rw [he']; exact hw)
  rw [maxCenter_eq_cRF hI hI𝔪, cRF_eq hI hI𝔪 hJ' hJ'i, hRF]

/-- **Theorem 3.3(1)**: all weights of `inv_𝔪(I)` are at most `1`. -/
theorem inv_le_one (i : ℕ) : inv I 𝔪 i ≤ 1 := by
  obtain ⟨n, e, he, hev⟩ := invAt_inv hI hI𝔪
  rw [← hev]
  by_cases hi : i < n
  · simp only [ext0, dite_eq_left hi]
    exact he.le_one (Iloc_le hI𝔪) _
  · simp only [ext0, dite_eq_right hi]
    norm_num

/-- `ord_𝔪(I)` is attained, bounds every `b` with `I A_𝔪 ⊆ 𝔪^b A_𝔪`, and is positive. -/
lemma ord_spec :
    Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ ord I 𝔪 ∧
    (∀ b : ℕ, Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ b → b ≤ ord I 𝔪) ∧
    1 ≤ ord I 𝔪 := by
  have hne : ({b : ℕ | Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ b}).Nonempty :=
    ⟨0, by simp⟩
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Iloc_ne_bot hI 𝔪)
  have hint := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Localization.AtPrime 𝔪))
    (maximalIdeal.isMaximal _).ne_top
  obtain ⟨N, hN⟩ : ∃ N : ℕ, f ∉ maximalIdeal (Localization.AtPrime 𝔪) ^ N := by
    by_contra h
    replace h := not_exists_not.1 h
    apply hf0
    rw [← Ideal.mem_bot, ← hint, Ideal.mem_iInf]
    exact h
  have hbdd : BddAbove {b : ℕ | Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ b} := by
    refine ⟨N, fun b hb => ?_⟩
    have hb' : Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ b := hb
    by_contra hbN
    exact hN (Ideal.pow_le_pow_right (not_le.1 hbN).le (hb' hf))
  have hord : ord I 𝔪 =
      sSup {b : ℕ | Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ b} := rfl
  rw [hord]
  refine ⟨Nat.sSup_mem hne hbdd, fun b hb => le_csSup hbdd hb, le_csSup hbdd ?_⟩
  show Iloc I 𝔪 ≤ _ ^ 1
  rw [pow_one]
  exact Iloc_le hI𝔪

/-- **Theorem 3.3(1)**: the first weight of `inv_𝔪(I)` is `1/ord_𝔪(I)`. -/
theorem inv_zero_eq_one_div_ord : inv I 𝔪 0 = 1 / ord I 𝔪 := by
  obtain ⟨hle, hmaxb, h1⟩ := ord_spec hI hI𝔪
  have hnle : ¬ Iloc I 𝔪 ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ (ord I 𝔪 + 1) := fun h => by
    have := hmaxb _ h
    omega
  have h0 : inv I 𝔪 0 ≠ 0 := InvAt.zero_ne hI (invAt_inv hI hI𝔪)
  obtain ⟨n, e, he, hev⟩ := invAt_inv hI hI𝔪
  have hn : 0 < n := by
    by_contra hn
    apply h0
    rw [← hev]
    simp only [ext0, dite_eq_right hn]
  have hinv0 : inv I 𝔪 0 = e ⟨0, hn⟩ := by
    rw [← hev]
    simp only [ext0, dite_eq_left hn]
  obtain ⟨J, hJ, rfl⟩ := he.1
  rw [hinv0]
  refine le_antisymm (he.zero_le_of_le_pow J.c J.centred (by omega) hle hn) ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  apply hnle
  refine hJ.trans ?_
  show J.c.RF J.e 1 ≤ _
  rw [Chart.RF, Ideal.span_le]
  rintro _ ⟨α, -, hα, rfl⟩
  have hb : (0 : ℚ) < ord I 𝔪 := by exact_mod_cast h1
  have he0 : 0 ≤ J.e ⟨0, hn⟩ := J.nonneg _
  have hsum : lam J.e α ≤ J.e ⟨0, hn⟩ * (α.degree : ℚ) := by
    rw [lam, Finsupp.degree_eq_sum, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi : J.e i ≤ J.e ⟨0, hn⟩ := J.anti (Fin.le_def.2 (Nat.zero_le _))
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)
  have hdeg : ord I 𝔪 + 1 ≤ α.degree := by
    by_contra hd
    replace hd := not_le.1 hd
    have hd' : (α.degree : ℚ) ≤ ord I 𝔪 := by exact_mod_cast Nat.lt_succ_iff.1 hd
    have h2 : J.e ⟨0, hn⟩ * ord I 𝔪 < 1 := by
      calc J.e ⟨0, hn⟩ * ord I 𝔪 < (1 / ord I 𝔪) * ord I 𝔪 := mul_lt_mul_of_pos_right hlt hb
        _ = 1 := one_div_mul_cancel hb.ne'
    linarith [mul_le_mul_of_nonneg_left hd' he0]
  have hmem : ∏ i, J.c.x i ^ α i ∈ maximalIdeal (Localization.AtPrime 𝔪) ^ α.degree := by
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (J.centred.x_mem i) _
  exact Ideal.pow_le_pow_right hdeg hmem

/-- **Theorem 3.3(1)**: the first weight has the form `1/a` for a positive integer `a`. -/
theorem exists_inv_zero_eq : ∃ a : ℕ, 0 < a ∧ inv I 𝔪 0 = 1 / a := by
  have h1 := (ord_spec hI hI𝔪).2.2
  exact ⟨ord I 𝔪, by omega, inv_zero_eq_one_div_ord hI hI𝔪⟩

/-- **Theorem 3.3(1)**: if `I A_𝔪 ⊆ 𝔪^b A_𝔪` (with `b ≥ 1`), the first weight is at most `1/b`. -/
theorem inv_zero_le_of_le_pow {b : ℕ} (hb : 0 < b)
    (hIb : I.map (algebraMap A (Localization.AtPrime 𝔪)) ≤ maximalIdeal (Localization.AtPrime 𝔪) ^ b) :
    inv I 𝔪 0 ≤ 1 / b := by
  rw [inv_zero_eq_one_div_ord hI hI𝔪]
  have hbord : b ≤ ord I 𝔪 := (ord_spec hI hI𝔪).2.1 b hIb
  exact one_div_le_one_div_of_le (by exact_mod_cast hb) (by exact_mod_cast hbord)

/-- **Theorem 3.3(1)** (`thm:invariant`), bundled. -/
theorem theorem_3_3_1 :
    (∃ J : MarkedCenter 𝔪, J.IsAdmissible I ∧ J.weights = inv I 𝔪) ∧
    (∀ J : MarkedCenter 𝔪, J.IsAdmissible I → toLex (inv I 𝔪) ≤ toLex J.weights) ∧
    (∀ J : MarkedCenter 𝔪, J.IsAdmissible I → J.weights = inv I 𝔪 →
      ∀ t, J.F t = maxCenter I 𝔪 t) ∧
    (∀ i, inv I 𝔪 i ≤ 1) ∧ inv I 𝔪 0 = 1 / ord I 𝔪 ∧
    (∃ a : ℕ, 0 < a ∧ inv I 𝔪 0 = 1 / a) ∧
    (∀ b : ℕ, 0 < b → I.map (algebraMap A (Localization.AtPrime 𝔪)) ≤
      maximalIdeal (Localization.AtPrime 𝔪) ^ b → inv I 𝔪 0 ≤ 1 / b) :=
  ⟨(isInvariant_inv hI hI𝔪).1, (isInvariant_inv hI hI𝔪).2,
    fun J hJ hw t => J.F_eq_maxCenter hI hI𝔪 hJ hw t, inv_le_one hI hI𝔪,
    inv_zero_eq_one_div_ord hI hI𝔪, exists_inv_zero_eq hI hI𝔪,
    fun _ hb hIb => inv_zero_le_of_le_pow hI hI𝔪 hb hIb⟩

end Part1

/-! ### Theorem 3.3(2): smooth invariance -/

/-- `B_𝔫` is a localization of a polynomial ring over `A_𝔪`, `𝔪 = 𝔫 ∩ A`: there are `r` and a
prime `Q` of `A_𝔪[X₁, …, X_r]` with `B_𝔫 ≅ A_𝔪[X₁, …, X_r]_Q` as `A`-algebras. -/
def IsLocalizationOfPolynomial (A : Type) {B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (𝔫 : Ideal B) [𝔫.IsPrime] : Prop :=
  ∃ (r : ℕ) (Q : Ideal (MvPolynomial (Fin r)
      (Localization.AtPrime (𝔫.comap (algebraMap A B))))) (_ : Q.IsPrime),
    Nonempty (Localization.AtPrime 𝔫 ≃ₐ[A] Localization.AtPrime Q)

/-- Smooth invariance along `A_𝔪[X₁, …, X_r]_Q ≅ B_𝔫`, with `𝔪` a free variable: `A → B` is
injective and the invariant of `IB` at `𝔫` is `inv_𝔪(I)`. -/
lemma invAt_map_of_localization_polynomial {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra.Smooth ℚ B] [Algebra A B] {I : Ideal A} (hI : I ≠ ⊥)
    (𝔫 : Ideal B) [𝔫.IsMaximal] (𝔪 : Ideal A) [𝔪.IsMaximal]
    (h𝔪 : 𝔫.comap (algebraMap A B) = 𝔪) (hI𝔪 : I ≤ 𝔪) {r : ℕ}
    (Q : Ideal (MvPolynomial (Fin r) (Localization.AtPrime 𝔪))) [Q.IsPrime]
    (φ : Localization.AtPrime 𝔫 ≃ₐ[A] Localization.AtPrime Q) :
    Function.Injective (algebraMap A B) ∧ InvAt (I.map (algebraMap A B)) 𝔫 (inv I 𝔪) := by
  classical
  -- the transition map `θ : A_𝔪[X] → B_𝔫`
  obtain ⟨θ, hθ⟩ : ∃ θ : MvPolynomial (Fin r) (Localization.AtPrime 𝔪) →+*
      Localization.AtPrime 𝔫, ∀ p, θ p = φ.symm (algebraMap _ (Localization.AtPrime Q) p) :=
    ⟨φ.symm.toRingEquiv.toRingHom.comp (algebraMap _ _), fun _ => rfl⟩
  have hAL : ∀ a : A, algebraMap A (Localization.AtPrime Q) a =
      algebraMap _ (Localization.AtPrime Q)
        (MvPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) a)) := fun a => by
    rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin r) (Localization.AtPrime 𝔪))
      (Localization.AtPrime Q), MvPolynomial.algebraMap_apply]
  have hAT : ∀ a : A, algebraMap A (Localization.AtPrime 𝔫) a =
      algebraMap B (Localization.AtPrime 𝔫) (algebraMap A B a) := fun a =>
    IsScalarTower.algebraMap_apply A B _ a
  have hinjS : Function.Injective (algebraMap A (Localization.AtPrime 𝔪)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔪)
  have hinjL : Function.Injective (algebraMap (MvPolynomial (Fin r) (Localization.AtPrime 𝔪))
      (Localization.AtPrime Q)) :=
    IsLocalization.injective (M := Q.primeCompl) (Localization.AtPrime Q)
      (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hθinj : Function.Injective θ := by
    intro p q h
    rw [hθ, hθ] at h
    exact hinjL (φ.symm.injective h)
  have hcomp : ∀ a : A, θ (MvPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) a)) =
      algebraMap B (Localization.AtPrime 𝔫) (algebraMap A B a) := by
    intro a
    rw [hθ, ← hAL, AlgEquiv.commutes, hAT]
  have hinjA : Function.Injective (algebraMap A B) := by
    intro a a' h
    have h2 : θ (MvPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) a)) =
        θ (MvPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) a')) := by
      rw [hcomp, hcomp, h]
    exact hinjS (MvPolynomial.C_injective _ _ (hθinj h2))
  -- `φ` and `φ⁻¹` preserve the maximal ideals
  have hmaxL : ∀ z, z ∈ maximalIdeal (Localization.AtPrime 𝔫) →
      φ z ∈ maximalIdeal (Localization.AtPrime Q) := by
    intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
    rwa [MulEquiv.isUnit_map]
  have hmaxT : ∀ z, z ∈ maximalIdeal (Localization.AtPrime Q) →
      φ.symm z ∈ maximalIdeal (Localization.AtPrime 𝔫) := by
    intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
    rwa [MulEquiv.isUnit_map]
  -- `Q` lies over the maximal ideal of `A_𝔪`
  have hQC : ∀ a ∈ maximalIdeal (Localization.AtPrime 𝔪), MvPolynomial.C a ∈ Q := by
    intro a ha
    obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl a
    change IsLocalization.mk' (Localization.AtPrime 𝔪) s t = a at hst
    subst hst
    have hs : s ∈ 𝔪 :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 s t).1 ha
    have hsn : algebraMap A B s ∈ 𝔫 := by
      have : s ∈ 𝔫.comap (algebraMap A B) := by rw [h𝔪]; exact hs
      exact this
    have h1 : algebraMap A (Localization.AtPrime 𝔫) s ∈
        maximalIdeal (Localization.AtPrime 𝔫) := by
      rw [hAT]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔫 _).2 hsn
    have h2 := hmaxL _ h1
    rw [AlgEquiv.commutes, hAL] at h2
    have h3 : MvPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) s) ∈ Q :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q _).1 h2
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul]
    exact Q.mul_mem_right _ h3
  have hloc : ∀ a ∈ maximalIdeal (Localization.AtPrime 𝔪),
      θ (MvPolynomial.C a) ∈ maximalIdeal (Localization.AtPrime 𝔫) := by
    intro a ha
    rw [hθ]
    exact hmaxT _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q _).2 (hQC a ha))
  have hsurj : ∀ z : Localization.AtPrime 𝔫, ∃ a b, IsUnit (θ b) ∧ z * θ b = θ a := by
    intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj Q.primeCompl (φ z)
    refine ⟨a, b, ?_, ?_⟩
    · rw [hθ]
      exact (IsLocalization.map_units (Localization.AtPrime Q) b).map φ.symm
    · rw [hθ, hθ]
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact hab
  -- transfer the invariant
  obtain ⟨n, e, he, hev⟩ := invAt_inv hI hI𝔪
  obtain ⟨J, -, -⟩ := he.1
  have := residueField_isIntegral 𝔫
  have hIS := IsInv.transfer_mvLoc θ hθinj hsurj hloc J.centred (Iloc_ne_bot hI 𝔪)
    (Iloc_le hI𝔪) he
  have hmapeq : (I.map (algebraMap A (Localization.AtPrime 𝔪))).map (θ.comp MvPolynomial.C) =
      (I.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime 𝔫)) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact hcomp a
  refine ⟨hinjA, n + r, pad (n + r) e, ?_, ?_⟩
  · show IsInv ((I.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime 𝔫))) _ _
    rw [← hmapeq]
    exact hIS
  · rw [ext0_pad (Nat.le_add_right n r)]
    exact hev

/-- **Theorem 3.3(2)** (smooth invariance). Let `A → B` be a homomorphism to a smooth finitely
generated `ℚ`-domain, `𝔫 ⊇ IB` a maximal ideal of `B`, and suppose that `B_𝔫` is a localization of
a polynomial ring over `A_𝔪`, `𝔪 = 𝔫 ∩ A`. Then `𝔪` is maximal and `inv_𝔫(IB) = inv_𝔪(I)`. -/
theorem inv_map_eq_of_localization_polynomial {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra.Smooth ℚ B] [Algebra A B] [IsScalarTower ℚ A B] {I : Ideal A} (hI : I ≠ ⊥)
    (𝔫 : Ideal B) [𝔫.IsMaximal] (hI𝔫 : I.map (algebraMap A B) ≤ 𝔫)
    (hloc : IsLocalizationOfPolynomial A 𝔫) :
    (𝔫.comap (algebraMap A B)).IsMaximal ∧
      inv (I.map (algebraMap A B)) 𝔫 = inv I (𝔫.comap (algebraMap A B)) := by
  have h𝔪 : (𝔫.comap (algebraMap A B)).IsMaximal := comap_isMaximal_of_finiteType 𝔫
  refine ⟨h𝔪, ?_⟩
  obtain ⟨r, Q, hQ, ⟨φ⟩⟩ := hloc
  have hI𝔪 : I ≤ 𝔫.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.1 hI𝔫
  obtain ⟨hinjA, hinv⟩ :=
    invAt_map_of_localization_polynomial hI 𝔫 (𝔫.comap (algebraMap A B)) rfl hI𝔪 Q φ
  have hIB : I.map (algebraMap A B) ≠ ⊥ := by
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    intro h
    have hmem : algebraMap A B f ∈ I.map (algebraMap A B) := Ideal.mem_map_of_mem _ hf
    rw [h, Ideal.mem_bot, ← map_zero (algebraMap A B)] at hmem
    exact hf0 (hinjA hmem)
  exact inv_eq_of_invAt hIB hI𝔫 hinv

/-! ### Theorem 3.3(3): the maximal locus -/

open Classical in
/-- The *maximal invariant* `maxinv(I)`: the largest invariant for `⪯` among the `inv_𝔪(I)`,
`𝔪 ⊇ I` maximal (Theorem 3.3(3)). -/
def maxinv (I : Ideal A) : ℕ → ℚ :=
  if h : ∃ v, (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ inv I 𝔪 = v) ∧
      ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 → inv I 𝔪 ⪯ v
  then h.choose else 0

/-- The ideal of the maximal locus: the intersection of the maximal ideals `𝔪 ⊇ I` with
`inv_𝔪(I) = maxinv(I)`. -/
def maxLocusIdeal (I : Ideal A) : Ideal A :=
  sInf {𝔪 | ∃ _ : 𝔪.IsMaximal, I ≤ 𝔪 ∧ inv I 𝔪 = maxinv I}

/-- The primes `𝔭₁, …, 𝔭ᵣ` of Theorem 3.3(3); `V(𝔭₁), …, V(𝔭ᵣ)` are the *components* of the
maximal locus. (They are the minimal primes over the ideal of the maximal locus.) -/
def components (I : Ideal A) : Set (Ideal A) := (maxLocusIdeal I).minimalPrimes

/-- `c(I)`, the number of components of the maximal locus. -/
def numComponents (I : Ideal A) : ℕ := (components I).ncard

/-- The number of nonzero entries of a weight vector supported on an initial segment. -/
lemma numNonzero_ext0 {n k : ℕ} {e : Fin n → ℚ} (h : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) :
    numNonzero (ext0 e) = min n k := by
  have hset : {i : ℕ | ext0 e i ≠ 0} = ↑(Finset.range (min n k)) := by
    ext i
    rw [Finset.coe_range, Set.mem_Iio, lt_min_iff]
    by_cases hi : i < n
    · change (if h : i < n then e ⟨i, h⟩ else 0) ≠ 0 ↔ _
      rw [dite_eq_left hi, h ⟨i, hi⟩]
      exact ⟨fun h' => ⟨hi, h'⟩, fun h' => h'.2⟩
    · change (if h : i < n then e ⟨i, h⟩ else 0) ≠ 0 ↔ _
      rw [dite_eq_right hi]
      simp [hi]
  rw [numNonzero, hset, Set.ncard_coe_finset, Finset.card_range]

section Part3

variable {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
include hI hItop

/-- **Theorem 3.3(3)**: `maxinv(I)` is attained and is the largest invariant for `⪯`. -/
theorem maxinv_spec :
    (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ inv I 𝔪 = maxinv I) ∧
      ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → inv I 𝔪 ⪯ maxinv I := by
  obtain ⟨v₀, ⟨𝔪₀, h𝔪₀, hI𝔪₀, hv₀⟩, hmax⟩ := exists_maxInv hI hItop
  have h : ∃ v, (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ inv I 𝔪 = v) ∧
      ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 → inv I 𝔪 ⪯ v :=
    ⟨v₀, ⟨𝔪₀, h𝔪₀, hI𝔪₀, inv_eq_of_invAt hI hI𝔪₀ hv₀⟩,
      fun 𝔪 _ hI𝔪 => hmax 𝔪 hI𝔪 _ (invAt_inv hI hI𝔪)⟩
  rw [maxinv, dite_eq_left h]
  exact h.choose_spec

/-- `maxinv(I)` bounds the engine invariants from below (in the lexicographic order). -/
lemma maxinv_le :
    ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex (maxinv I) ≤ toLex v := by
  intro 𝔪 _ hI𝔪 v hv
  rw [← inv_eq_of_invAt hI hI𝔪 hv]
  exact (maxinv_spec hI hItop).2 𝔪 hI𝔪

omit hItop in
/-- The ideal of the maximal locus is the engine's `locusIdeal`. -/
lemma maxLocusIdeal_eq : maxLocusIdeal I = locusIdeal I (maxinv I) := by
  unfold maxLocusIdeal locusIdeal maxLocus
  congr 1
  ext 𝔪
  constructor
  · rintro ⟨h𝔪, hI𝔪, heq⟩
    exact ⟨h𝔪, hI𝔪, heq ▸ invAt_inv hI hI𝔪⟩
  · rintro ⟨h𝔪, hI𝔪, hv⟩
    exact ⟨h𝔪, hI𝔪, inv_eq_of_invAt hI hI𝔪 hv⟩

/-- The weights of `maxinv(I)` have a common denominator. -/
lemma exists_weights_maxinv : ∃ d : ℕ, 0 < d ∧ ∀ i, ∃ w : ℕ, (w : ℚ) = d * maxinv I i := by
  obtain ⟨⟨𝔪, h𝔪, hI𝔪, heq⟩, -⟩ := maxinv_spec hI hItop
  obtain ⟨n, e, he, hev⟩ := invAt_inv hI hI𝔪
  rw [← heq, ← hev]
  refine exists_weights (N := n) (fun i => ?_) (fun i hi => ?_)
  · simp only [ext0]
    split_ifs
    · exact he.nonneg _
    · exact le_rfl
  · simp only [ext0, dite_eq_right (not_lt.2 hi)]

/-- **Theorem 3.3(3)** (`thm:invariant`): the maximal locus. There are finitely many primes
`𝔭₁, …, 𝔭ᵣ ⊇ I` with `𝔭ᵢ + 𝔭ⱼ = A` for `i ≠ j` such that `inv_𝔪(I) = maxinv(I)` exactly when `𝔪`
contains some `𝔭ᵢ`; if `k` is the number of nonzero entries of `maxinv(I)` and `𝔪 ⊇ 𝔭ᵢ`, there is a
regular system of parameters `x` of `A_𝔪` with `𝔭ᵢ A_𝔪 = (x₁, …, x_k)` such that `(x, maxinv(I))`
is admissible for `I` at `𝔪`. -/
theorem theorem_3_3_3 :
    (components I).Finite ∧
    (∀ 𝔭 ∈ components I, 𝔭.IsPrime ∧ I ≤ 𝔭) ∧
    (∀ 𝔭 ∈ components I, ∀ 𝔭' ∈ components I, 𝔭 ≠ 𝔭' → 𝔭 ⊔ 𝔭' = ⊤) ∧
    (∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 →
      (inv I 𝔪 = maxinv I ↔ ∃ 𝔭 ∈ components I, 𝔭 ≤ 𝔪)) ∧
    (∀ 𝔭 ∈ components I, ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 →
      ∃ J : MarkedCenter 𝔪, J.weights = maxinv I ∧ J.IsAdmissible I ∧
        𝔭.map (algebraMap A (Localization.AtPrime 𝔪)) =
          Ideal.span (J.x '' {i | (i : ℕ) < numNonzero (maxinv I)})) := by
  have hmax := maxinv_le hI hItop
  have hcomp : components I = (locusIdeal I (maxinv I)).minimalPrimes := by
    rw [components, maxLocusIdeal_eq hI]
  refine ⟨Ideal.finite_minimalPrimes_of_isNoetherianRing A _, fun 𝔭 h𝔭 => ⟨h𝔭.1.1, ?_⟩,
    fun 𝔭 h𝔭 𝔭' h𝔭' hne => ?_, fun 𝔪 _ hI𝔪 => ⟨fun heq => ?_, ?_⟩, fun 𝔭 h𝔭 𝔪 _ h𝔭𝔪 => ?_⟩
  · -- `I ⊆ 𝔭`
    refine le_trans ?_ h𝔭.1.2
    exact le_sInf (by rintro 𝔪 ⟨-, hI𝔪, -⟩; exact hI𝔪)
  · -- disjointness
    rw [hcomp] at h𝔭 h𝔭'
    exact minimalPrimes_sup_eq_top hI hmax h𝔭 h𝔭' hne
  · -- points of maximal invariant lie on a component
    have h𝔪L : maxLocusIdeal I ≤ 𝔪 := sInf_le ⟨inferInstance, hI𝔪, heq⟩
    obtain ⟨𝔭, h𝔭, h𝔭𝔪⟩ := Ideal.exists_minimalPrimes_le h𝔪L
    exact ⟨𝔭, h𝔭, h𝔭𝔪⟩
  · -- points on a component have maximal invariant
    rintro ⟨𝔭, h𝔭, h𝔭𝔪⟩
    rw [hcomp] at h𝔭
    exact inv_eq_of_invAt hI hI𝔪 (mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪).2
  · -- local structure along a component
    rw [hcomp] at h𝔭
    obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI hmax h𝔭 𝔪 h𝔭𝔪
    obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hI𝔪 hv
    have hp : 𝔭 = D.p := D.eq_p_of_minimal h𝔭 h𝔭𝔪
    let J' : MC (Localization.AtPrime 𝔪) D.n :=
      ⟨Loc.transport (D.ctrl 𝔪 D.hg) D.ck, D.ek, D.cent, D.inv.nonneg, D.inv.anti⟩
    have hadm : (MarkedCenter.ofMC J').IsAdmissible I := by
      show Iloc I 𝔪 ≤ (MarkedCenter.ofMC J').F 1
      rw [MarkedCenter.ofMC_F]
      obtain ⟨⟨J₀, hJ₀, hJ₀e⟩, -⟩ := D.inv
      exact hJ₀.trans (D.rf 𝔪 D.hg J₀ hJ₀ hJ₀e 1).le
    have hnum : numNonzero (maxinv I) = min D.n D.k := by
      have h := numNonzero_ext0 D.supp
      rw [D.hv] at h
      exact h
    have hk : ∀ i : Fin D.n, (i : ℕ) < numNonzero (maxinv I) ↔ (i : ℕ) < D.k := by
      intro i
      rw [hnum, lt_min_iff]
      exact ⟨fun h => h.2, fun h => ⟨i.2, h⟩⟩
    have hset : {i : Fin D.n | (i : ℕ) < numNonzero (maxinv I)} =
        {i : Fin D.n | (i : ℕ) < D.k} :=
      Set.ext hk
    have hmap : 𝔭.map (algebraMap A (Localization.AtPrime 𝔪)) =
        Ideal.span ((Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x ''
          {i : Fin D.n | (i : ℕ) < numNonzero (maxinv I)}) := by
      rw [hset, hp, D.map_p]
      rfl
    exact ⟨MarkedCenter.ofMC J', D.hv, hadm, hmap⟩

end Part3

/-! ### Theorem 3.3(4): the global center -/

/-- The global center `F_t` of `I` retaining the component `V(𝔭)`:
`F_t = {f ∈ A : f ∈ F_t(𝔪) for every maximal ideal 𝔪 ⊇ 𝔭}`. -/
def globalCenter (I 𝔭 : Ideal A) (t : ℚ) : Ideal A :=
  ⨅ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal) (_ : 𝔭 ≤ 𝔪),
    (maxCenter I 𝔪 t).comap (algebraMap A (Localization.AtPrime 𝔪))

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
lemma mem_globalCenter {I 𝔭 : Ideal A} {t : ℚ} {f : A} :
    f ∈ globalCenter I 𝔭 t ↔ ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 →
      algebraMap A (Localization.AtPrime 𝔪) f ∈ maxCenter I 𝔪 t := by
  simp only [globalCenter, Submodule.mem_iInf, Ideal.mem_comap]

/-- **Theorem 3.3(4)** (`thm:invariant`): `F_t A_𝔪 = F_t(𝔪)` for every maximal `𝔪 ⊇ 𝔭` and
`F_t A_𝔪 = A_𝔪` for every maximal `𝔪 ⊉ 𝔭`. -/
theorem theorem_3_3_4 {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) {𝔭 : Ideal A}
    (h𝔭 : 𝔭 ∈ components I) (t : ℚ) :
    (∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 →
      (globalCenter I 𝔭 t).map (algebraMap A (Localization.AtPrime 𝔪)) = maxCenter I 𝔪 t) ∧
    (∀ (𝔪 : Ideal A) [𝔪.IsMaximal], ¬ 𝔭 ≤ 𝔪 →
      (globalCenter I 𝔭 t).map (algebraMap A (Localization.AtPrime 𝔪)) = ⊤) := by
  have hmax := maxinv_le hI hItop
  rw [components, maxLocusIdeal_eq hI] at h𝔭
  have hIL : I ≤ locusIdeal I (maxinv I) := le_sInf (by rintro 𝔪 ⟨-, hI𝔪, -⟩; exact hI𝔪)
  have hI𝔭 : I ≤ 𝔭 := hIL.trans h𝔭.1.2
  have hG : globalCenter I 𝔭 t = compF I 𝔭 t := by
    ext f
    rw [mem_globalCenter, mem_compF]
    constructor
    · intro h 𝔪 _ h𝔭𝔪
      have := h 𝔪 h𝔭𝔪
      rwa [maxCenter_eq_cRF hI (hI𝔭.trans h𝔭𝔪)] at this
    · intro h 𝔪 _ h𝔭𝔪
      rw [maxCenter_eq_cRF hI (hI𝔭.trans h𝔭𝔪)]
      exact h 𝔪 h𝔭𝔪
  refine ⟨fun 𝔪 _ h𝔭𝔪 => ?_, fun 𝔪 _ h𝔭𝔪 => ?_⟩
  · rw [hG, compF_map hI hmax h𝔭 𝔪 h𝔭𝔪 t, maxCenter_eq_cRF hI (hI𝔭.trans h𝔭𝔪)]
  · obtain ⟨d, hd, hw⟩ := exists_weights_maxinv hI hItop
    rw [hG]
    exact compF_map_of_not_le hI hmax h𝔭 hd hw 𝔪 h𝔭𝔪 t

/-! ### Theorem 3.3(5): well-ordering -/

/-- The product of the denominators (in lowest terms) of the first `i` entries of `e`. -/
def denProd (e : ℕ → ℚ) (i : ℕ) : ℕ := ∏ j ∈ Finset.range i, (e j).den

/-- The set `Γ` of Theorem 3.3(5): weight vectors each of whose positive entries has the form
`D!/a` with `a ∈ ℕ_{>0}`, where `D` is the product of the denominators of the previous entries,
and after a zero entry every entry is zero. -/
def Γ : Set (ℕ → ℚ) :=
  {e | (∀ i, e i = 0 ∨ ∃ a : ℕ, 0 < a ∧ e i = ((denProd e i).factorial : ℚ) / a) ∧
    ∀ i, e i = 0 → e (i + 1) = 0}

/-- **Theorem 3.3(5)**: `Γ` contains all invariants. -/
theorem inv_mem_Γ {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) :
    inv I 𝔪 ∈ Γ := by
  have hv := invAt_inv hI hI𝔪
  refine ⟨InvAt.goodV hI hI𝔪 hv, fun i hi => ?_⟩
  obtain ⟨n, e, he, hev⟩ := hv
  rw [← hev] at hi ⊢
  simp only [ext0] at hi ⊢
  by_cases h1 : i + 1 < n
  · rw [dite_eq_left h1]
    rw [dite_eq_left (show i < n by omega)] at hi
    have h2 : e ⟨i + 1, h1⟩ ≤ e ⟨i, by omega⟩ := he.anti (Fin.le_def.2 (Nat.le_succ i))
    exact le_antisymm (h2.trans hi.le) (he.nonneg _)
  · rw [dite_eq_right h1]

/-- Elements of `Γ` with at most `N` nonzero entries vanish from the index `N` on. -/
lemma eq_zero_of_mem_Γ {N : ℕ} {e : ℕ → ℚ} (he : e ∈ Γ) (hN : {i | e i ≠ 0}.encard ≤ N)
    {i : ℕ} (hi : N ≤ i) : e i = 0 := by
  by_contra hne
  have hprop : ∀ j k, e j = 0 → e (j + k) = 0 := by
    intro j k h0
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [← Nat.add_assoc]
      exact he.2 _ ih
  have hall : ∀ j ≤ i, e j ≠ 0 := by
    intro j hj h0
    apply hne
    have := hprop j (i - j) h0
    rwa [Nat.add_sub_of_le hj] at this
  have hsub : {j : ℕ | j < i + 1} ⊆ {j | e j ≠ 0} := fun j hj => hall j (Nat.lt_succ_iff.1 hj)
  have h1 := (Set.encard_le_encard hsub).trans hN
  rw [Set.Nat.encard_range] at h1
  have h2 : i + 1 ≤ N := by exact_mod_cast h1
  omega

/-- **Theorem 3.3(5)**: for every `N`, the elements of `Γ` with at most `N` nonzero entries are
well-ordered by `⪯`: there is no infinite strictly `⪯`-decreasing sequence among them. -/
theorem Γ_wellFoundedOn (N : ℕ) :
    {e ∈ Γ | {i | e i ≠ 0}.encard ≤ N}.WellFoundedOn (· ≺ ·) := by
  rw [Set.wellFoundedOn_iff]
  refine Subrelation.wf (r := InvImage (· < ·) (encW N)) ?_ (InvImage.wf _ wellFounded_lt)
  intro a b ⟨hab, ha, hb⟩
  exact encW_lt hb.1.1 ha.1.1 (fun i hi => eq_zero_of_mem_Γ hb.1 hb.2 hi)
    (fun i hi => eq_zero_of_mem_Γ ha.1 ha.2 hi) (weightLT_iff.1 hab)

/-- The computation in the justification of the enlargement of `Γ` in Theorem 3.3(5): if the
weights `e₁, …, e_r` have been chosen, `D` is the product of their denominators, and
`0 < 1 - ∑ βᵢ eᵢ ≤ 1` with `βᵢ ∈ ℕ`, then for every `q ∈ ℕ_{>0}`,
`(1 - ∑ βᵢ eᵢ)/q = D!/a` for some `a ∈ ℕ_{>0}`. -/
theorem next_weight_form {r : ℕ} (e : Fin r → ℚ) (β : Fin r → ℕ) {q : ℕ} (hq : 0 < q)
    (h0 : 0 < 1 - ∑ i, (β i : ℚ) * e i) (h1 : 1 - ∑ i, (β i : ℚ) * e i ≤ 1) :
    ∃ a : ℕ, 0 < a ∧ (1 - ∑ i, (β i : ℚ) * e i) / q = ((∏ i, (e i).den).factorial : ℚ) / a := by
  obtain ⟨D, hD⟩ : ∃ D, D = ∏ i, (e i).den := ⟨_, rfl⟩
  rw [← hD]
  have hDpos : 0 < D := hD ▸ Finset.prod_pos fun i _ => (e i).den_pos
  -- `D · ∑ βᵢ eᵢ` is an integer `z`
  have hint : ∃ z : ℤ, (D : ℚ) * ∑ i, (β i : ℚ) * e i = z := by
    have : ∀ i, ∃ z : ℤ, (D : ℚ) * ((β i : ℚ) * e i) = z := by
      intro i
      obtain ⟨z, hz⟩ := dvd_den_mul_int (D := D)
        (hD ▸ Finset.dvd_prod_of_mem (fun i => (e i).den) (Finset.mem_univ i))
      exact ⟨β i * z, by push_cast; rw [← hz]; ring⟩
    choose z hz using this
    refine ⟨∑ i, z i, ?_⟩
    rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hz i
  obtain ⟨z, hz⟩ := hint
  have hDq : (0 : ℚ) < D := by exact_mod_cast hDpos
  have hzlt : z < D := by
    have : (z : ℚ) < D := by rw [← hz]; nlinarith
    exact_mod_cast this
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := by rw [← hz]; nlinarith
    exact_mod_cast this
  -- the numerator `m = D - z` satisfies `1 ≤ m ≤ D`, hence `m ∣ D!`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = D - z := ⟨(D - z).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hm1 : 1 ≤ m := by omega
  have hmle : m ≤ D := by omega
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (by omega : 0 < m) hmle
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      exact absurd hk (Nat.factorial_pos D).ne'
    · exact h
  refine ⟨D * q * k, Nat.mul_pos (Nat.mul_pos hDpos hq) hk0, ?_⟩
  have hmq : (m : ℚ) = D - z := by exact_mod_cast hm
  have hD' : (D : ℚ) ≠ 0 := hDq.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have h1' : 1 - ∑ i, (β i : ℚ) * e i = (m : ℚ) / D := by
    rw [hmq, ← hz, eq_div_iff hD']
    ring
  rw [h1', hk]
  push_cast
  rw [div_div, div_eq_div_iff (mul_ne_zero hD' hq') (mul_ne_zero (mul_ne_zero hD' hq') hk')]
  ring

end BezoutCounterexample
