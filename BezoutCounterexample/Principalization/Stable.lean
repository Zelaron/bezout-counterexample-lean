import BezoutCounterexample.Principalization.Globalize

/-!
# Derivation-stability of the canonical centre and the length bound

Lemma 3.7 (`lem:derivations`) of the paper.

* `IsRun.map`: Method-1 runs push forward along ring maps with compatible charts.
* `Chart.polynomial`, `Chart.polyLoc`: the chart `(x, t)` on `S[t]` and on `S[t]_{(𝔪,t)}`.
* `expHom`, `truncEvalHom`, `flowHom`: the flow `f ↦ ∑ tᵐ δᵐ f / m!` of a derivation, a ring
  homomorphism modulo `tᴺ`.
* `deriv_mem_RF` (**derivation-stability**): if `δ I ⊆ I`, then `δ` maps each coordinate
  `xᵢ` of the maximal admissible centre of `I` into `𝓕_{eᵢ}`.  The proof compares, on
  `S[t]_{(𝔪,t)}` and for the ideal `I + (tᴺ)`, the centre `(x, t^{N})` with its image under the
  truncated flow, using uniqueness of the maximal centre, and extracts the `t`-coefficient.
* `length_le_of_derivations`: `m` stabilizing derivations independent at the closed point bound
  the length of the invariant by `n - m`.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] {R' : Type*} [CommRing R'] [Algebra ℚ R']
  {n n' : ℕ} {hnn : n ≤ n'}

lemma pad_nextE {j : ℕ} (hj : j < n) (e : Fin n → ℚ) (b : ℚ) :
    pad n' (nextE e j b) = nextE (pad n' e) j b := by
  funext i
  by_cases h1 : (i : ℕ) < j
  · rw [pad_nextE_lt i h1]; simp only [nextE, if_pos h1]
  · by_cases h2 : (i : ℕ) = j
    · rw [pad_nextE_eq hj i h2]; simp only [nextE, if_neg h1, if_pos h2]
    · have : pad n' (nextE e j b) i = 0 := by
        simp only [pad]; split_ifs with h
        · simp only [nextE, Fin.val_mk, if_neg h1, if_neg h2]
        · rfl
      rw [this]; simp only [nextE, if_neg h1, if_neg h2]

lemma pushIdx_sub_single (β : Fin n →₀ ℕ) (l : Fin n) :
    pushIdx hnn (β - Finsupp.single l 1) =
      pushIdx hnn β - Finsupp.single (Fin.castLE hnn l) 1 := by
  ext i
  by_cases hi : (i : ℕ) < n
  · obtain ⟨a, rfl⟩ : ∃ a : Fin n, Fin.castLE hnn a = i := ⟨⟨i, hi⟩, Fin.ext rfl⟩
    rw [pushIdx_apply, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_tsub, Pi.sub_apply,
      pushIdx_apply]
    simp only [Finsupp.single_apply, (Fin.castLE_injective hnn).eq_iff]
  · rw [pushIdx_apply_ge hnn _ i (by omega), Finsupp.coe_tsub, Pi.sub_apply,
      pushIdx_apply_ge hnn _ i (by omega), zero_tsub]

lemma nextChart_congr (c : Chart S n) {jj jj' l : Fin n} (hjj : jj = jj') {g g' : S} (hg : g = g')
    (u u' : Sˣ) (hu : c.d l g = u) (hu' : c.d l g' = u') :
    nextChart c jj l g u hu = nextChart c jj' l g' u' hu' := by
  subst hjj; subst hg
  have : u = u' := Units.ext (by rw [← hu, ← hu'])
  subst this; rfl

/-- **Runs push forward** along ring homomorphisms with compatible charts. -/
theorem IsRun.map {ψ : S →+* R'} {I : Ideal S} {j : ℕ} {c : Chart S n} {e : Fin n → ℚ}
    {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ} (h : IsRun I j c e k ck ek) :
    ∀ c' : Chart R' n', Compat hnn ψ c c' →
      ∃ ck' : Chart R' n', IsRun (I.map ψ) j c' (pad n' e) k ck' (pad n' ek) ∧
        Compat hnn ψ ck ck' ∧ ∀ i : Fin n', n ≤ (i : ℕ) → ck'.x i = c'.x i := by
  induction h with
  | refl j c e => exact fun c' hc => ⟨c', .refl _ _ _, hc, fun _ _ => rfl⟩
  | @step j c e k ck ek hj f hf β l hl hβl hlam hN hunit hb u hu hnext ih =>
    intro c' hc
    have hj' : j < n' := lt_of_lt_of_le hj hnn
    set g := c.Dv (β - Finsupp.single l 1) f with hg
    obtain ⟨ck', hrun', hck', hext⟩ := ih _ (hc.nextChart ⟨j, hj⟩ l g u hu)
    refine ⟨ck', ?_, hck', fun i hi => ?_⟩
    swap
    · rw [hext i hi]
      have h1 : i ≠ Fin.castLE hnn ⟨j, hj⟩ := fun h' => by
        rw [h'] at hi; simp at hi; omega
      have h2 : i ≠ Fin.castLE hnn l := fun h' => by rw [h'] at hi; simp at hi; omega
      simp only [Principalization.nextChart, Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne h1 h2]
      rw [Chart.replace_x_ne _ _ _ _ _ h2]
    have hβ' : pushIdx hnn β (Fin.castLE hnn l) ≠ 0 := by rw [pushIdx_apply]; exact hβl
    have hlam' : lam (pad n' e) (pushIdx hnn β) < 1 := by rw [lam_pad]; exact hlam
    have hN' : 0 < tailSum j (pushIdx hnn β) := by rw [tailSum_push]; exact hN
    have hunit' : IsUnit (c'.D (pushIdx hnn β) (ψ f)) := by rw [hc.D]; exact hunit.map ψ
    have hW : nextW (pad n' e) j (pushIdx hnn β) = nextW e j β := by
      simp only [nextW, lam_pad, tailSum_push]
    have hb' : ∀ i : Fin n', (i : ℕ) < j → nextW (pad n' e) j (pushIdx hnn β) ≤ pad n' e i := by
      intro i hi
      rw [hW]
      have hin : (i : ℕ) < n := lt_trans hi hj
      simp only [pad, dif_pos hin]
      exact hb ⟨i, hin⟩ hi
    have hg' : c'.Dv (pushIdx hnn β - Finsupp.single (Fin.castLE hnn l) 1) (ψ f) = ψ g := by
      rw [← pushIdx_sub_single, hc.Dv]
    have hu' : c'.d (Fin.castLE hnn l)
        (c'.Dv (pushIdx hnn β - Finsupp.single (Fin.castLE hnn l) 1) (ψ f)) =
          ↑(Units.map ψ.toMonoidHom u) := by
      rw [hg']; exact hc.hu' hu
    refine IsRun.step hj' (ψ f) (Ideal.mem_map_of_mem ψ hf) (pushIdx hnn β) (Fin.castLE hnn l)
      (by simpa using hl) hβ' hlam' hN' hunit' hb' (Units.map ψ.toMonoidHom u) hu' ?_
    rw [hW, ← pad_nextE hj]
    have : nextChart c' ⟨j, hj'⟩ (Fin.castLE hnn l)
        (c'.Dv (pushIdx hnn β - Finsupp.single (Fin.castLE hnn l) 1) (ψ f))
        (Units.map ψ.toMonoidHom u) hu' =
      nextChart c' (Fin.castLE hnn ⟨j, hj⟩) (Fin.castLE hnn l) (ψ g)
        (Units.map ψ.toMonoidHom u) (hc.hu' hu) :=
      nextChart_congr c' (Fin.ext rfl) hg' _ _ _ _
    rw [this]; exact hrun'

/-- Runs for an ideal are runs for any larger ideal. -/
lemma IsRun.mono {I I' : Ideal S} (hII : I ≤ I') {j : ℕ} {c : Chart S n} {e : Fin n → ℚ}
    {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ} (h : IsRun I j c e k ck ek) :
    IsRun I' j c e k ck ek := by
  induction h with
  | refl => exact .refl _ _ _
  | step hj f hf β l hl hβl hlam hN hunit hb u hu hnext ih =>
    exact .step hj f (hII hf) β l hl hβl hlam hN hunit hb u hu ih

/-- Concatenation of runs. -/
lemma IsRun.trans {I : Ideal S} {j : ℕ} {c : Chart S n} {e : Fin n → ℚ}
    {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ} (h : IsRun I j c e k ck ek)
    {m : ℕ} {cm : Chart S n} {em : Fin n → ℚ} (h' : IsRun I k ck ek m cm em) :
    IsRun I j c e m cm em := by
  induction h with
  | refl => exact h'
  | step hj f hf β l hl hβl hlam hN hunit hb u hu hnext ih =>
    exact .step hj f hf β l hl hβl hlam hN hunit hb u hu (ih h')

lemma Compat.id (c : Chart S n) : Compat (le_refl n) (RingHom.id S) c c :=
  ⟨fun i => by simp [Fin.castLE_refl], fun i f => by simp [Fin.castLE_refl],
    fun i hi f => absurd i.2 (by omega)⟩

/-- Iterated derivatives of powers of a function `y` with `δ y = 1`. -/
lemma iterate_pow_of_eq_one (δ : Derivation ℚ S S) {y : S} (hy : δ y = 1) (N m : ℕ) :
    δ^[m] (y ^ N) = (N.descFactorial m : S) * y ^ (N - m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, Derivation.leibniz_pow, hy,
      smul_eq_mul, smul_eq_mul, nsmul_eq_mul, mul_one]
    have hδN : δ (N.descFactorial m : S) = 0 := by
      rw [← nsmul_one, map_nsmul, Derivation.map_one_eq_zero, smul_zero]
    rw [hδN, smul_zero, add_zero, Nat.descFactorial_succ]
    rcases Nat.lt_or_ge m N with hmN | hmN
    · rw [show N - m = (N - (m + 1)) + 1 by omega, Nat.add_sub_cancel]
      push_cast
      ring
    · rw [Nat.sub_eq_zero_of_le hmN, Nat.sub_eq_zero_of_le (by omega : N ≤ m + 1)]
      simp [Nat.sub_eq_zero_of_le hmN]

lemma Chart.D_single (c : Chart S n) (l : Fin n) (m : ℕ) (f : S) :
    c.D (Finsupp.single l m) f = (c.d l)^[m] f := by
  rw [Chart.D, Chart.dpow_single]
  simp only [Chart.dd, SubmonoidClass.coe_pow, Module.End.pow_apply]
  rfl

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open TrivSqZeroExt Polynomial

section Poly

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- The extension of a derivation `δ` of `S` to `S[X]` (acting on coefficients) with `X ↦ v`,
as a ring map to the square-zero extension. -/
def polyTsze (δ : Derivation ℚ S S) (v : S[X]) : S[X] →+* TrivSqZeroExt S[X] S[X] :=
  Polynomial.eval₂RingHom (derivToTsze (S := S[X]) δ) (inl X + inr v)

lemma polyTsze_C (δ : Derivation ℚ S S) (v : S[X]) (a : S) :
    polyTsze δ v (C a) = derivToTsze (S := S[X]) δ a := by
  simp [polyTsze]

lemma polyTsze_X (δ : Derivation ℚ S S) (v : S[X]) : polyTsze δ v X = inl X + inr v := by
  simp [polyTsze]

lemma fst_polyTsze (δ : Derivation ℚ S S) (v : S[X]) (p : S[X]) : (polyTsze δ v p).fst = p := by
  have : (fstHom S[X] S[X] S[X]).toRingHom.comp (polyTsze δ v) = RingHom.id S[X] := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, polyTsze_C, RingHom.id_apply]
      exact fst_derivToTsze δ a
    · simp [polyTsze_X]
  exact congrArg (fun f : S[X] →+* S[X] => f p) this

/-- The derivation of `S[X]` extending `δ` with `X ↦ v`. -/
def polyExt (δ : Derivation ℚ S S) (v : S[X]) : Derivation ℚ S[X] S[X] where
  toFun p := (polyTsze δ v p).snd
  map_add' p q := by simp
  map_smul' r p := by
    change (polyTsze δ v (r • p)).snd = r • (polyTsze δ v p).snd
    rw [Algebra.smul_def, map_mul, snd_mul, fst_polyTsze, smul_eq_mul]
    have h0 : (polyTsze δ v (algebraMap ℚ S[X] r)).snd = 0 := by
      rw [IsScalarTower.algebraMap_apply ℚ S S[X], Polynomial.algebraMap_eq, polyTsze_C,
        snd_derivToTsze, Derivation.map_algebraMap, map_zero]
    rw [h0, smul_zero, add_zero, ← Algebra.smul_def]
  map_one_eq_zero' := by
    change (polyTsze δ v 1).snd = 0
    rw [map_one, snd_one]
  leibniz' p q := by
    change (polyTsze δ v (p * q)).snd = p • (polyTsze δ v q).snd + q • (polyTsze δ v p).snd
    rw [map_mul, snd_mul, fst_polyTsze, fst_polyTsze]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

@[simp] lemma polyExt_C (δ : Derivation ℚ S S) (v : S[X]) (a : S) :
    polyExt δ v (C a) = C (δ a) := by
  change (polyTsze δ v (C a)).snd = _
  rw [polyTsze_C, snd_derivToTsze, Polynomial.algebraMap_eq]

@[simp] lemma polyExt_X (δ : Derivation ℚ S S) (v : S[X]) : polyExt δ v X = v := by
  change (polyTsze δ v X).snd = _
  simp [polyTsze_X]

variable {n : ℕ}

/-- The coordinates of the polynomial chart. -/
def polyX (c : Chart S n) : Fin (n + 1) → S[X] := Fin.lastCases X (fun j => C (c.x j))

/-- The derivations of the polynomial chart. -/
def polyD (c : Chart S n) : Fin (n + 1) → Derivation ℚ S[X] S[X] :=
  Fin.lastCases (polyExt 0 1) (fun j => polyExt (c.d j) 0)

@[simp] lemma polyX_last (c : Chart S n) : polyX c (Fin.last n) = X := by
  simp [polyX]

@[simp] lemma polyX_castSucc (c : Chart S n) (j : Fin n) : polyX c (Fin.castSucc j) = C (c.x j) := by
  simp [polyX]

@[simp] lemma polyD_last (c : Chart S n) : polyD c (Fin.last n) = polyExt 0 1 := by
  simp [polyD]

@[simp] lemma polyD_castSucc (c : Chart S n) (j : Fin n) :
    polyD c (Fin.castSucc j) = polyExt (c.d j) 0 := by
  simp [polyD]

/-- The Kähler differentials of `S[X]` are spanned by those of `S` and `dX`. -/
lemma span_polynomial (c : Chart S n) :
    Submodule.span S[X] (Set.range fun i : Fin (n + 1) =>
      KaehlerDifferential.D ℚ S[X] (polyX c i)) = ⊤ := by
  set W := Submodule.span S[X] (Set.range fun i : Fin (n + 1) =>
      KaehlerDifferential.D ℚ S[X] (polyX c i))
  have hX : KaehlerDifferential.D ℚ S[X] X ∈ W :=
    Submodule.subset_span ⟨Fin.last n, by simp⟩
  have hC : ∀ a : S, KaehlerDifferential.D ℚ S[X] (C a) ∈ W := by
    intro a
    have h1 : KaehlerDifferential.D ℚ S[X] (C a) =
        KaehlerDifferential.map ℚ ℚ S S[X] (KaehlerDifferential.D ℚ S a) := by
      rw [KaehlerDifferential.map_D]; rfl
    rw [h1, c.kD_eq_sum a, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, KaehlerDifferential.map_D]
    rw [← algebraMap_smul S[X] ((c.d j) a), Polynomial.algebraMap_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castSucc j, by simp⟩)
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add]; exact W.add_mem hp hq
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, Derivation.leibniz]
    exact W.add_mem (W.smul_mem _ hX) (W.smul_mem _ ih)

lemma polyD_polyX (c : Chart S n) (i j : Fin (n + 1)) :
    polyD c i (polyX c j) = if i = j then 1 else 0 := by
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => simp
    | cast j =>
      rw [polyD_last, polyX_castSucc, polyExt_C, if_neg (Fin.castSucc_lt_last j).ne']
      simp
  | cast i =>
    cases j using Fin.lastCases with
    | last => rw [polyD_castSucc, polyX_last, polyExt_X, if_neg (Fin.castSucc_lt_last i).ne]
    | cast j =>
      rw [polyD_castSucc, polyX_castSucc, polyExt_C, c.d_x]
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, if_neg (fun h' => h (Fin.castSucc_injective _ h')), map_zero]

/-- The chart `(x, X)` on `S[X]` (the new coordinate `X` is the last one). -/
def Chart.polynomial (c : Chart S n) : Chart S[X] (n + 1) where
  x := polyX c
  d := polyD c
  d_x := polyD_polyX c
  span := span_polynomial c

@[simp] lemma Chart.polynomial_x_last (c : Chart S n) : c.polynomial.x (Fin.last n) = X :=
  polyX_last c

@[simp] lemma Chart.polynomial_x_castSucc (c : Chart S n) (j : Fin n) :
    c.polynomial.x (Fin.castSucc j) = C (c.x j) := polyX_castSucc c j

@[simp] lemma Chart.polynomial_d_last (c : Chart S n) :
    c.polynomial.d (Fin.last n) = polyExt 0 1 := polyD_last c

@[simp] lemma Chart.polynomial_d_castSucc (c : Chart S n) (j : Fin n) :
    c.polynomial.d (Fin.castSucc j) = polyExt (c.d j) 0 := polyD_castSucc c j

lemma castLE_succ_eq (j : Fin n) : Fin.castLE (Nat.le_succ n) j = Fin.castSucc j := rfl

/-- The polynomial chart extends the chart along `C`. -/
lemma Chart.compat_polynomial (c : Chart S n) :
    Compat (Nat.le_succ n) (Polynomial.C : S →+* S[X]) c c.polynomial := by
  refine ⟨fun i => ?_, fun i f => ?_, fun i hi f => ?_⟩
  · rw [castLE_succ_eq, Chart.polynomial_x_castSucc]
  · rw [castLE_succ_eq, Chart.polynomial_d_castSucc, polyExt_C]
  · have : i = Fin.last n := Fin.ext (by have := i.2; simp at hi ⊢; omega)
    subst this
    simp

end Poly

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open Polynomial IsLocalRing

section PolyLoc

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}

variable (S) in
/-- The maximal ideal `(𝔪, X)` of `S[X]`. -/
def polyMax : Ideal S[X] := RingHom.ker ((residue S).comp (Polynomial.evalRingHom 0))

lemma mem_polyMax (p : S[X]) : p ∈ polyMax S ↔ p.coeff 0 ∈ maximalIdeal S := by
  rw [polyMax, RingHom.mem_ker, RingHom.comp_apply, Polynomial.coe_evalRingHom,
    residue_eq_zero_iff, Polynomial.coeff_zero_eq_eval_zero]

instance polyMax_isMaximal : (polyMax S).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun a => by
    obtain ⟨b, rfl⟩ := residue_surjective a
    exact ⟨C b, by simp⟩)

lemma X_mem_polyMax : (X : S[X]) ∈ polyMax S := by simp [mem_polyMax]

lemma C_mem_polyMax {a : S} (ha : a ∈ maximalIdeal S) : C a ∈ polyMax S := by
  simpa [mem_polyMax] using ha

/-- The local ring `S[X]_{(𝔪, X)}`. -/
abbrev PolyLoc (S : Type*) [CommRing S] [IsLocalRing S] := Localization.AtPrime (polyMax S)

/-- The chart `(x, X)` on `S[X]_{(𝔪, X)}`. -/
def Chart.polyLoc (c : Chart S n) : Chart (PolyLoc S) (n + 1) :=
  c.polynomial.localization (polyMax S).primeCompl

/-- The inclusion `S → S[X]_{(𝔪, X)}`. -/
def toPolyLoc : S →+* PolyLoc S := (algebraMap S[X] (PolyLoc S)).comp Polynomial.C

/-- The variable `X` in `S[X]_{(𝔪, X)}`. -/
def polyT : PolyLoc S := algebraMap S[X] (PolyLoc S) X

lemma Chart.polyLoc_x_last (c : Chart S n) : c.polyLoc.x (Fin.last n) = polyT := by
  simp [Chart.polyLoc, polyT]

lemma Chart.polyLoc_x_castSucc (c : Chart S n) (j : Fin n) :
    c.polyLoc.x (Fin.castSucc j) = toPolyLoc (c.x j) := by
  simp [Chart.polyLoc, toPolyLoc]

lemma Chart.compat_polyLoc (c : Chart S n) :
    Compat (Nat.le_succ n) (toPolyLoc : S →+* PolyLoc S) c c.polyLoc := by
  have h := c.compat_polynomial
  refine ⟨fun i => ?_, fun i f => ?_, fun i hi f => ?_⟩
  · simp only [Chart.polyLoc, Chart.localization_x, h.x i]; rfl
  · simp only [Chart.polyLoc, toPolyLoc, RingHom.comp_apply]
    rw [Chart.localization_d, h.d]
  · simp only [Chart.polyLoc, toPolyLoc, RingHom.comp_apply]
    rw [Chart.localization_d, h.d_extra i hi, map_zero]

lemma polyMax_eq_span (c : Chart S n) (hc : c.IsCentred) :
    polyMax S = Ideal.span (Set.range c.polynomial.x) := by
  apply le_antisymm
  · intro p hp
    rw [mem_polyMax] at hp
    obtain ⟨q, hq⟩ := (Polynomial.X_dvd_sub_C (p := p))
    have hsub : p = C (p.coeff 0) + X * q := by rw [← hq]; ring
    rw [hsub]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Fin.last n, by simp⟩))
    have hC : Ideal.map (Polynomial.C : S →+* S[X]) (maximalIdeal S) ≤
        Ideal.span (Set.range c.polynomial.x) := by
      rw [hc, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨Fin.castSucc j, by simp⟩
    exact hC (Ideal.mem_map_of_mem _ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last => simpa [Chart.polynomial] using X_mem_polyMax
    | cast j =>
      simp only [Chart.polynomial_x_castSucc]
      exact C_mem_polyMax (hc.x_mem j)

lemma Chart.polyLoc_isCentred (c : Chart S n) (hc : c.IsCentred) : c.polyLoc.IsCentred := by
  rw [Chart.IsCentred, ← Localization.AtPrime.map_eq_maximalIdeal]
  have h := polyMax_eq_span c hc
  calc Ideal.map (algebraMap S[X] (PolyLoc S)) (polyMax S)
      = Ideal.map (algebraMap S[X] (PolyLoc S)) (Ideal.span (Set.range c.polynomial.x)) := by
        rw [← h]
    _ = Ideal.span (Set.range c.polyLoc.x) := by
        rw [Ideal.map_span, ← Set.range_comp]; rfl

end PolyLoc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open Finset

section Flow

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- The general Leibniz rule for iterates of a derivation. -/
lemma iterate_leibniz (δ : Derivation ℚ S S) (m : ℕ) (f g : S) :
    δ^[m] (f * g) = ∑ p ∈ antidiagonal m, m.choose p.1 • (δ^[p.1] f * δ^[p.2] g) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (M := S) (fun i j => δ^[i] f * δ^[j] g) m]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, nsmul_add, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [m.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.1 hij).symm, mul_comm]

/-- The formal flow `f ↦ ∑ δᵐ f / m! Xᵐ`. -/
def expSeries (δ : Derivation ℚ S S) (f : S) : PowerSeries S :=
  PowerSeries.mk fun m => ((m.factorial : ℚ)⁻¹) • δ^[m] f

lemma coeff_expSeries (δ : Derivation ℚ S S) (f : S) (m : ℕ) :
    PowerSeries.coeff m (expSeries δ f) = ((m.factorial : ℚ)⁻¹) • δ^[m] f := by
  simp [expSeries]

lemma expSeries_mul (δ : Derivation ℚ S S) (f g : S) :
    expSeries δ (f * g) = expSeries δ f * expSeries δ g := by
  ext m
  rw [coeff_expSeries, PowerSeries.coeff_mul, iterate_leibniz, smul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_expSeries, coeff_expSeries, smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have key : ((m.choose p.1 : ℕ) : ℚ) * (p.2.factorial : ℚ) * (p.1.factorial : ℚ) =
      (m.factorial : ℚ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial p.2 p.1
    rw [add_comm p.2 p.1, hp] at this
    exact_mod_cast this
  have h1 : (p.1.factorial : ℚ) ≠ 0 := by positivity
  have h2 : (p.2.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((m.choose p.1 : ℕ) : ℚ) ≠ 0 := by
    have : 0 < m.choose p.1 := Nat.choose_pos (by omega)
    positivity
  rw [← key]
  field_simp

lemma iterate_derivation_add (δ : Derivation ℚ S S) (m : ℕ) (f g : S) :
    δ^[m] (f + g) = δ^[m] f + δ^[m] g := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_add, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

lemma iterate_derivation_zero (δ : Derivation ℚ S S) (m : ℕ) : δ^[m] (0 : S) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]

lemma expSeries_add (δ : Derivation ℚ S S) (f g : S) :
    expSeries δ (f + g) = expSeries δ f + expSeries δ g := by
  ext m
  simp only [coeff_expSeries, map_add, iterate_derivation_add, smul_add]

lemma expSeries_one (δ : Derivation ℚ S S) : expSeries δ 1 = 1 := by
  ext m
  rw [coeff_expSeries, PowerSeries.coeff_one]
  rcases m with _ | m
  · simp
  · rw [Function.iterate_succ_apply, Derivation.map_one_eq_zero, iterate_derivation_zero]
    simp

/-- The flow as a ring homomorphism `S → S⟦X⟧`. -/
def expHom (δ : Derivation ℚ S S) : S →+* PowerSeries S where
  toFun := expSeries δ
  map_one' := expSeries_one δ
  map_mul' := expSeries_mul δ
  map_zero' := by ext m; simp [coeff_expSeries, iterate_derivation_zero]
  map_add' := expSeries_add δ

variable {T : Type*} [CommRing T]

/-- Truncated evaluation of power series at `t`. -/
def truncEval (t : T) (N : ℕ) (g : PowerSeries T) : T := Polynomial.eval t (PowerSeries.trunc N g)

lemma truncEval_eq_sum (t : T) (N : ℕ) (g : PowerSeries T) :
    truncEval t N g = ∑ m ∈ range N, PowerSeries.coeff m g * t ^ m := by
  rw [truncEval, ← Polynomial.eval₂_id, PowerSeries.eval₂_trunc_eq_sum_range]
  rfl

lemma eval_sub_truncEval_mem (t : T) (N : ℕ) (p : Polynomial T) :
    Polynomial.eval t p - truncEval t N (p : PowerSeries T) ∈ Ideal.span {t ^ N} := by
  have hdvd : Polynomial.X ^ N ∣ p - PowerSeries.trunc N (p : PowerSeries T) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  rw [truncEval, ← Polynomial.eval_sub, hq, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

lemma truncEval_mul_mem (t : T) (N : ℕ) (g h : PowerSeries T) :
    truncEval t N (g * h) - truncEval t N g * truncEval t N h ∈ Ideal.span {t ^ N} := by
  have h1 : truncEval t N (g * h) =
      truncEval t N ((PowerSeries.trunc N g * PowerSeries.trunc N h : Polynomial T) :
        PowerSeries T) := by
    rw [truncEval, truncEval, Polynomial.coe_mul, PowerSeries.trunc_trunc_mul_trunc]
  have h2 : truncEval t N g * truncEval t N h =
      Polynomial.eval t (PowerSeries.trunc N g * PowerSeries.trunc N h) := by
    rw [Polynomial.eval_mul]; rfl
  rw [h1, h2, ← neg_sub, neg_mem_iff]
  exact eval_sub_truncEval_mem t N _

/-- Truncated evaluation as a ring homomorphism to `T ⧸ (tᴺ)`. -/
def truncEvalHom (t : T) (N : ℕ) (hN : 0 < N) : PowerSeries T →+* T ⧸ Ideal.span {t ^ N} where
  toFun g := Ideal.Quotient.mk _ (truncEval t N g)
  map_one' := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [truncEval, PowerSeries.trunc_one, Polynomial.eval_one, map_one]
  map_mul' g h := by
    rw [← map_mul, Ideal.Quotient.eq]
    exact truncEval_mul_mem t N g h
  map_zero' := by simp [truncEval]
  map_add' g h := by simp [truncEval, map_add]

end Flow

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open TrivSqZeroExt Polynomial IsLocalRing

section Dual

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S]

/-- `p ↦ (p(0), p'(0))` on `S[X]`. -/
def dualEval : S[X] →+* TrivSqZeroExt S S :=
  Polynomial.eval₂RingHom (inlHom S S) (inr 1)

lemma fst_dualEval (p : S[X]) : (dualEval p).fst = p.coeff 0 := by
  have : (fstHom S S S).toRingHom.comp dualEval = Polynomial.evalRingHom 0 := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_ <;> simp [dualEval]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact congrArg (fun f : S[X] →+* S => f p) this

lemma dualEval_isUnit (p : (polyMax S).primeCompl) : IsUnit (dualEval (p : S[X])) := by
  rw [isUnit_iff_isUnit_fst, fst_dualEval]
  have h := p.2
  rw [Ideal.mem_primeCompl_iff, mem_polyMax] at h
  exact (IsLocalRing.notMem_maximalIdeal.1 h)

/-- The map `S[X]_{(𝔪,X)} → S[ε]/(ε²)`, `a ↦ a`, `X ↦ ε`. -/
def dualLoc : PolyLoc S →+* TrivSqZeroExt S S :=
  IsLocalization.lift (M := (polyMax S).primeCompl) dualEval_isUnit

@[simp] lemma dualLoc_toPolyLoc (a : S) : dualLoc (toPolyLoc a) = inl a := by
  simp [dualLoc, toPolyLoc, IsLocalization.lift_eq, dualEval]

@[simp] lemma dualLoc_polyT : dualLoc (polyT : PolyLoc S) = inr 1 := by
  simp [dualLoc, polyT, IsLocalization.lift_eq, dualEval]

/-- Elements of an ideal generated by elements whose `dualLoc`-components lie in `A ≤ B` have the
same property. -/
lemma dualLoc_span {G : Set (PolyLoc S)} {A B : Ideal S} (hAB : A ≤ B)
    (hG : ∀ g ∈ G, (dualLoc g).fst ∈ A ∧ (dualLoc g).snd ∈ B) :
    ∀ g ∈ Ideal.span G, (dualLoc g).fst ∈ A ∧ (dualLoc g).snd ∈ B := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, fst_add, snd_add]; exact ⟨A.add_mem hx.1 hy.1, B.add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, fst_mul, snd_mul]
    refine ⟨A.mul_mem_left _ hx.1, B.add_mem ?_ ?_⟩
    · rw [smul_eq_mul]; exact B.mul_mem_left _ hx.2
    · rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      exact B.mul_mem_left _ (hAB hx.1)

end Dual

section Swap

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

/-- Monomials in a chart obtained by replacing the last coordinate and swapping it to
position `k`. -/
lemma prod_nextChart_last (B : Chart R (n + 1)) {k : ℕ} (hk : k < n + 1) (g : R) (u : Rˣ)
    (hu : B.d (Fin.last n) g = u) (α : Fin (n + 1) →₀ ℕ) :
    ∏ i, (nextChart B ⟨k, hk⟩ (Fin.last n) g u hu).x i ^ α i =
      (∏ a : Fin n, B.x (Fin.castSucc a) ^ α (Equiv.swap ⟨k, hk⟩ (Fin.last n) (Fin.castSucc a))) *
        g ^ α ⟨k, hk⟩ := by
  set σ := Equiv.swap (⟨k, hk⟩ : Fin (n + 1)) (Fin.last n)
  simp only [nextChart, Chart.reindex_x]
  rw [← Equiv.prod_comp σ (fun i => (B.replace (Fin.last n) g u hu).x (σ i) ^ α i)]
  simp only [Equiv.swap_apply_self, σ]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [Chart.replace_x_ne _ _ _ _ _ (Fin.castSucc_lt_last a).ne]
  · rw [Chart.replace_x_self, Equiv.swap_apply_right]

lemma sum_swap_last {M : Type*} [AddCommMonoid M] {k : ℕ} (hk : k < n + 1) (F : Fin (n + 1) → M) :
    ∑ i, F i = (∑ a : Fin n, F (Equiv.swap ⟨k, hk⟩ (Fin.last n) (Fin.castSucc a))) +
      F ⟨k, hk⟩ := by
  rw [← Equiv.sum_comp (Equiv.swap (⟨k, hk⟩ : Fin (n + 1)) (Fin.last n)), Fin.sum_univ_castSucc,
    Equiv.swap_apply_right]

/-- The weights after the extra step, pulled back to the old coordinates. -/
lemma nextE_pad_swap {ek : Fin n → ℚ} {k : ℕ} (hk : k < n + 1)
    (hz : ∀ a : Fin n, k ≤ (a : ℕ) → ek a = 0) (b : ℚ) (a : Fin n) :
    nextE (pad (n + 1) ek) k b (Equiv.swap ⟨k, hk⟩ (Fin.last n) (Fin.castSucc a)) = ek a := by
  by_cases hak : (a : ℕ) = k
  · have : Fin.castSucc a = ⟨k, hk⟩ := Fin.ext (by simp [hak])
    rw [this, Equiv.swap_apply_left, hz a hak.ge]
    simp only [nextE, Fin.val_last]
    have : ¬ n < k := by have := a.2; omega
    have : n ≠ k := by have := a.2; omega
    simp [*]
  · have h1 : Fin.castSucc a ≠ ⟨k, hk⟩ := fun h => hak (by simpa using congrArg Fin.val h)
    have h2 : Fin.castSucc a ≠ Fin.last n := (Fin.castSucc_lt_last a).ne
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    simp only [nextE, Fin.coe_castSucc]
    by_cases hlt : (a : ℕ) < k
    · rw [if_pos hlt]; simp [pad, a.2]
    · rw [if_neg hlt, if_neg hak, hz a (by omega)]

lemma nextE_pad_at {ek : Fin n → ℚ} {k : ℕ} (hk : k < n + 1) (b : ℚ) :
    nextE (pad (n + 1) ek) k b ⟨k, hk⟩ = b := by
  simp [nextE]

end Swap

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open TrivSqZeroExt Polynomial IsLocalRing

section FlowFacts

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S]

/-- The truncated flow `φ_N f = ∑_{m<N} tᵐ δᵐ f / m!` in `S[X]_{(𝔪,X)}`. -/
def flowN (δ : Derivation ℚ S S) (N : ℕ) (f : S) : PolyLoc S :=
  truncEval polyT N (PowerSeries.map toPolyLoc (expHom δ f))

lemma flowN_eq_sum (δ : Derivation ℚ S S) (N : ℕ) (f : S) :
    flowN δ N f = ∑ m ∈ Finset.range N,
      toPolyLoc (((m.factorial : ℚ)⁻¹) • δ^[m] f) * polyT ^ m := by
  rw [flowN, truncEval_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [PowerSeries.coeff_map]
  congr 2
  exact coeff_expSeries δ f m

lemma flowN_succ (δ : Derivation ℚ S S) (M : ℕ) (f : S) :
    flowN δ (M + 1) f = toPolyLoc f + polyT * ∑ m ∈ Finset.range M,
      toPolyLoc (((m + 1).factorial : ℚ)⁻¹ • δ^[m + 1] f) * polyT ^ m := by
  rw [flowN_eq_sum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, Function.iterate_zero, id_eq,
    pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma dualLoc_flowN (δ : Derivation ℚ S S) {N : ℕ} (hN : 2 ≤ N) (f : S) :
    dualLoc (flowN δ N f) = inl f + inr (δ f) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  rw [flowN_eq_sum, map_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  have hvan : ∀ m ∈ Finset.range M, dualLoc (toPolyLoc (((m + 1 + 1).factorial : ℚ)⁻¹ •
      δ^[m + 1 + 1] f) * polyT ^ (m + 1 + 1)) = 0 := by
    intro m _
    rw [map_mul, map_pow, dualLoc_polyT, pow_succ, pow_succ, mul_assoc, inr_mul_inr, mul_zero,
      mul_zero]
  rw [Finset.sum_eq_zero hvan, zero_add]
  simp only [map_mul, map_pow, dualLoc_polyT, dualLoc_toPolyLoc, zero_add, pow_zero, mul_one,
    pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    Function.iterate_zero, id_eq, Function.iterate_one]
  rw [add_comm]
  congr 1
  rw [inl_mul_inr, smul_eq_mul, mul_one]

/-- The flow modulo `tᴺ` as a ring homomorphism. -/
def flowHom (δ : Derivation ℚ S S) (N : ℕ) (hN : 0 < N) :
    S →+* PolyLoc S ⧸ Ideal.span {(polyT : PolyLoc S) ^ N} :=
  (truncEvalHom polyT N hN).comp ((PowerSeries.map toPolyLoc).comp (expHom δ))

lemma flowHom_apply (δ : Derivation ℚ S S) (N : ℕ) (hN : 0 < N) (f : S) :
    flowHom δ N hN f = Ideal.Quotient.mk _ (flowN δ N f) := rfl

end FlowFacts

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open Polynomial IsLocalRing

lemma isUnit_det_of_lowerTri {R : Type*} [CommRing R] [IsLocalRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (hup : ∀ i j, i < j → M i j ∈ maximalIdeal R)
    (hdiag : ∀ i, M i i - 1 ∈ maximalIdeal R) : IsUnit M.det := by
  have h1 : residue R M.det = 1 := by
    rw [RingHom.map_det, Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have := hdiag i
      rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at this
      simpa [RingHom.mapMatrix_apply] using this
    · intro i j hij
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      exact (residue_eq_zero_iff _).2 (hup i j (by simpa using hij))
  by_contra h
  have : M.det ∈ maximalIdeal R := h
  rw [← residue_eq_zero_iff, h1] at this
  exact one_ne_zero this

section FlowChart

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}

lemma polyLoc_d_toPolyLoc (ck : Chart S n) (a : Fin n) (f : S) :
    ck.polyLoc.d (Fin.castSucc a) (toPolyLoc f) = toPolyLoc (ck.d a f) :=
  ck.compat_polyLoc.d a f

lemma polyLoc_d_polyT (ck : Chart S n) (i : Fin (n + 1)) :
    ck.polyLoc.d i polyT = if i = Fin.last n then 1 else 0 := by
  rw [← ck.polyLoc_x_last, ck.polyLoc.d_x]

lemma polyT_mem_maximal : (polyT : PolyLoc S) ∈ maximalIdeal (PolyLoc S) := by
  rw [polyT, IsLocalization.AtPrime.to_map_mem_maximal_iff (PolyLoc S) (polyMax S)]
  exact X_mem_polyMax

lemma flow_jac_isUnit (ck : Chart S n) (y : Fin n → PolyLoc S)
    (hy : ∀ a, ∃ h, y a = toPolyLoc (ck.x a) + polyT * h) :
    IsUnit (ck.polyLoc.jac (Fin.lastCases polyT y)).det := by
  have ht : (polyT : PolyLoc S) ∈ maximalIdeal (PolyLoc S) := polyT_mem_maximal
  apply isUnit_det_of_lowerTri
  · intro i j hij
    simp only [Chart.jac, Matrix.of_apply]
    cases j using Fin.lastCases with
    | last =>
      rw [Fin.lastCases_last, polyLoc_d_polyT, if_neg hij.ne]; exact zero_mem _
    | cast b =>
      rw [Fin.lastCases_castSucc]
      cases i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last _))
      | cast a =>
        obtain ⟨h, hh⟩ := hy b
        have hab : a ≠ b := fun h' => by rw [h'] at hij; exact lt_irrefl _ hij
        rw [hh, map_add, polyLoc_d_toPolyLoc, Derivation.leibniz, polyLoc_d_polyT,
          if_neg (Fin.castSucc_lt_last a).ne, smul_zero, add_zero, ck.d_x, if_neg hab,
          map_zero, zero_add, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ ht
  · intro i
    cases i using Fin.lastCases with
    | last => simp [Chart.jac, polyLoc_d_polyT]
    | cast a =>
      obtain ⟨h, hh⟩ := hy a
      simp only [Chart.jac, Matrix.of_apply, Fin.lastCases_castSucc]
      rw [hh, map_add, polyLoc_d_toPolyLoc, ck.d_x, if_pos rfl, map_one, Derivation.leibniz,
        polyLoc_d_polyT, if_neg (Fin.castSucc_lt_last a).ne, smul_zero, add_zero,
        add_sub_cancel_left, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ ht

lemma Chart.IsCentred.change' {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {m : ℕ}
    {c : Chart R m} (hc : c.IsCentred) (y : Fin m → R) (hy : IsUnit (c.jac y).det)
    (h : Ideal.span (Set.range y) = Ideal.span (Set.range c.x)) : (c.change y hy).IsCentred := by
  change maximalIdeal R = Ideal.span (Set.range y)
  rw [h]; exact hc

lemma flow_span_eq (ck : Chart S n) (y : Fin n → PolyLoc S)
    (hy : ∀ a, ∃ h, y a = toPolyLoc (ck.x a) + polyT * h) :
    Ideal.span (Set.range (Fin.lastCases polyT y)) = Ideal.span (Set.range ck.polyLoc.x) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last => exact Ideal.subset_span ⟨Fin.last n, by simp [Chart.polyLoc_x_last]⟩
    | cast a =>
      obtain ⟨h, hh⟩ := hy a
      simp only [Fin.lastCases_castSucc]
      rw [hh]
      refine Ideal.add_mem _ (Ideal.subset_span ⟨Fin.castSucc a, by simp [Chart.polyLoc_x_castSucc]⟩)
        (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Fin.last n, by simp [Chart.polyLoc_x_last]⟩))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last => exact Ideal.subset_span ⟨Fin.last n, by simp [Chart.polyLoc_x_last]⟩
    | cast a =>
      obtain ⟨h, hh⟩ := hy a
      have h1 : toPolyLoc (ck.x a) ∈ Ideal.span (Set.range (Fin.lastCases polyT y)) := by
        have : toPolyLoc (ck.x a) = y a - polyT * h := by rw [hh]; ring
        rw [this]
        refine Ideal.sub_mem _ (Ideal.subset_span ⟨Fin.castSucc a, by simp⟩)
          (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Fin.last n, by simp⟩))
      rw [Chart.polyLoc_x_castSucc]; exact h1

end FlowChart

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open Polynomial IsLocalRing TrivSqZeroExt

lemma IsRun.stage_le {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ} {I : Ideal S} {j : ℕ}
    {c : Chart S n} {e : Fin n → ℚ} {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ}
    (h : IsRun I j c e k ck ek) (hj : j ≤ n) : k ≤ n := by
  induction h with
  | refl => exact hj
  | step hj' f hf β l hl hβl hlam hN hunit hb u hu hnext ih => exact ih (by omega)

lemma tailSum_single_ge {n : ℕ} {j : ℕ} {l : Fin n} (hl : j ≤ (l : ℕ)) (m : ℕ) :
    tailSum j (Finsupp.single l m) = m := by
  classical
  rw [tailSum, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; rw [Finsupp.single_apply, if_neg (Ne.symm hb)]
  · intro h; exfalso; exact h (Finset.mem_filter.2 ⟨Finset.mem_univ l, hl⟩)

lemma pad_zero' {n n' : ℕ} : pad n' (0 : Fin n → ℚ) = 0 := by
  funext i; simp [pad]

lemma nextE_pad_antitone {n n' : ℕ} {ek : Fin n → ℚ} (hnn : ∀ i, 0 ≤ ek i) (hanti : Antitone ek)
    {k : ℕ} (hkn : k ≤ n) {b : ℚ} (hb0 : 0 ≤ b) (hb : ∀ a : Fin n, (a : ℕ) < k → b ≤ ek a) :
    Antitone (nextE (pad n' ek) k b) := by
  have hpad : ∀ i : Fin n', ∀ hi : (i : ℕ) < k, pad n' ek i = ek ⟨i, by omega⟩ := fun i hi => by
    simp [pad, show (i : ℕ) < n by omega]
  have hpnn : ∀ i : Fin n', 0 ≤ pad n' ek i := fun i => by
    simp only [pad]; split_ifs
    · exact hnn _
    · exact le_rfl
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  simp only [nextE]
  by_cases hj : (j : ℕ) < k
  · have hi : (i : ℕ) < k := lt_of_le_of_lt hij' hj
    rw [if_pos hi, if_pos hj, hpad i hi, hpad j hj]
    exact hanti (show (⟨i, _⟩ : Fin n) ≤ ⟨j, _⟩ from hij')
  · by_cases hjk : (j : ℕ) = k
    · rw [if_neg hj, if_pos hjk]
      by_cases hi : (i : ℕ) < k
      · rw [if_pos hi, hpad i hi]; exact hb _ hi
      · rw [if_neg hi, if_pos (by omega)]
    · rw [if_neg hj, if_neg hjk]
      split_ifs
      · exact hpnn i
      · exact hb0
      · exact le_rfl

section K

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}

instance polyLoc_noetherian : IsNoetherianRing (PolyLoc S) :=
  IsLocalization.isNoetherianRing (polyMax S).primeCompl _ inferInstance

/-- **Derivations preserving an ideal preserve its canonical centre** (on each coordinate). -/
theorem deriv_mem_RF {I : Ideal S} {c : Chart S n} {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ}
    (hrun : IsRun I 0 c 0 k ck ek) (hadm : I ≤ ck.RF ek 1) (hck : ck.IsCentred)
    (hnn : ∀ i, 0 ≤ ek i) (hanti : Antitone ek) (hsupp : ∀ i, ek i ≠ 0 ↔ (i : ℕ) < k)
    (δ : Derivation ℚ S S) (hδ : ∀ f ∈ I, δ f ∈ I) (i : Fin n) (hi : (i : ℕ) < k) :
    δ (ck.x i) ∈ ck.RF ek (ek i) := by
  classical
  obtain ⟨d, w, hd, hw⟩ := Chart.exists_scale hnn
  set N := d + 1 with hNdef
  have hN : 0 < N := by omega
  have hN2 : 2 ≤ N := by omega
  have hkn : k ≤ n := hrun.stage_le (Nat.zero_le _)
  have hk1 : k < n + 1 := by omega
  have hz : ∀ a : Fin n, k ≤ (a : ℕ) → ek a = 0 := fun a ha => by
    by_contra h; exact absurd ((hsupp a).1 h) (by omega)
  have hpos : ∀ a : Fin n, (a : ℕ) < k → (1 : ℚ) / d ≤ ek a := by
    intro a ha
    have h1 : ek a ≠ 0 := (hsupp a).2 ha
    have h2 : (w a : ℚ) = d * ek a := hw a
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hw1 : 1 ≤ w a := by
      by_contra h; push_neg at h
      have : w a = 0 := by omega
      rw [this, Nat.cast_zero] at h2
      exact h1 ((mul_eq_zero.1 h2.symm).resolve_left hdq.ne')
    rw [div_le_iff₀ hdq, mul_comm, ← h2]; exact_mod_cast hw1
  -- the ring `S' = S[t]_{(𝔪,t)}`
  set t : PolyLoc S := polyT with htdef
  set ψ : S →+* PolyLoc S := toPolyLoc with hψdef
  -- Step 1: push the run forward
  obtain ⟨ck', hrun', hcompat, hext⟩ :=
    hrun.map (hnn := Nat.le_succ n) c.polyLoc c.compat_polyLoc
  have hck' : ck' = ck.polyLoc := by
    refine Chart.eq_of_x (funext fun j => ?_)
    cases j using Fin.lastCases with
    | last => rw [hext _ (by simp), c.polyLoc_x_last, ck.polyLoc_x_last]
    | cast a => rw [← castLE_succ_eq, hcompat.x a, ← ck.compat_polyLoc.x a]
  rw [hck', pad_zero'] at hrun'
  -- Step 2: one more step with `tᴺ`
  set C := ck.polyLoc with hCdef
  set It : Ideal (PolyLoc S) := I.map ψ ⊔ Ideal.span {t ^ N} with hItdef
  have htN : t ^ N ∈ It := Ideal.mem_sup_right (Ideal.subset_span rfl)
  have hCx : C.x (Fin.last n) = t := ck.polyLoc_x_last
  have hCd : C.d (Fin.last n) t = 1 := by rw [← hCx, C.d_x]; simp
  have hcastN : ∀ m : ℕ, (m : PolyLoc S) = algebraMap ℚ (PolyLoc S) m := fun m => by simp
  have hNunit : IsUnit ((N : ℕ) : PolyLoc S) := by
    rw [hcastN]; exact (isUnit_iff_ne_zero.2 (by exact_mod_cast hN.ne')).map _
  have hfunit : IsUnit ((N.factorial : ℕ) : PolyLoc S) := by
    rw [hcastN]; exact (isUnit_iff_ne_zero.2 (by exact_mod_cast (Nat.factorial_pos N).ne')).map _
  set β : Fin (n + 1) →₀ ℕ := Finsupp.single (Fin.last n) N with hβdef
  have hβsub : β - Finsupp.single (Fin.last n) 1 = Finsupp.single (Fin.last n) (N - 1) := by
    rw [hβdef]; ext j
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have hDv : C.Dv (β - Finsupp.single (Fin.last n) 1) (t ^ N) = (N : PolyLoc S) * t := by
    rw [hβsub, Chart.Dv, Chart.D_single, iterate_pow_of_eq_one _ hCd]
    have hfact : (∏ j, ((Finsupp.single (Fin.last n) (N - 1)) j).factorial) = (N - 1).factorial := by
      rw [Finset.prod_eq_single (Fin.last n)]
      · simp
      · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
      · simp
    rw [hfact, show N - (N - 1) = 1 by omega, pow_one, ← smul_mul_assoc]
    congr 1
    have hdesc : N.descFactorial (N - 1) = N * (N - 1).factorial := by
      have h := Nat.factorial_mul_descFactorial (show N - 1 ≤ N by omega)
      rw [show N - (N - 1) = 1 by omega, Nat.factorial_one, one_mul] at h
      rw [h, Nat.mul_factorial_pred (by omega : N ≠ 0)]
    rw [hdesc, Algebra.smul_def, hcastN, hcastN N, ← map_mul]
    congr 1
    have : ((N - 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  set u : (PolyLoc S)ˣ := hNunit.unit with hudef
  have hu : C.d (Fin.last n) (C.Dv (β - Finsupp.single (Fin.last n) 1) (t ^ N)) = ↑u := by
    rw [hDv, Derivation.leibniz, hCd, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul,
      mul_one, hudef, IsUnit.unit_spec]
  have hlam : lam (pad (n + 1) ek) β < 1 := by
    rw [hβdef, lam_single]
    simp [pad]
  have hNt : 0 < tailSum k β := by rw [tailSum_single_ge (by simp; omega)]; exact hN
  have hunit : IsUnit (C.D β (t ^ N)) := by
    rw [hβdef, Chart.D_single, iterate_pow_of_eq_one _ hCd, Nat.descFactorial_self, Nat.sub_self,
      pow_zero, mul_one]
    exact hfunit
  have hW : nextW (pad (n + 1) ek) k β = 1 / N := by
    rw [nextW, tailSum_single_ge (by simp; omega)]
    rw [hβdef, lam_single]
    simp [pad]
  have hb : ∀ i : Fin (n + 1), (i : ℕ) < k → nextW (pad (n + 1) ek) k β ≤ pad (n + 1) ek i := by
    intro i hi
    rw [hW]
    have hin : (i : ℕ) < n := by omega
    simp only [pad, dif_pos hin]
    refine le_trans ?_ (hpos ⟨i, hin⟩ hi)
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    rw [hNdef]; push_cast
    exact one_div_le_one_div_of_le hdq (by linarith)
  have hstep := IsRun.step (I := It) hk1 (t ^ N) htN β (Fin.last n) (by simp; omega)
    (by simp [hβdef]) hlam hNt hunit hb u hu (IsRun.refl _ _ _)
  have hfull := (hrun'.mono (le_sup_left : I.map ψ ≤ It)).trans hstep
  -- Step 3: the transfer bound on `S'`
  set C'' := nextChart C ⟨k, hk1⟩ (Fin.last n) (C.Dv (β - Finsupp.single (Fin.last n) 1) (t ^ N))
    u hu with hC''def
  set Et := nextE (pad (n + 1) ek) k (nextW (pad (n + 1) ek) k β) with hEtdef
  obtain ⟨C3, hC3, hbound⟩ := hfull.transfer_bound (hnn := le_refl (n + 1)) (Compat.id c.polyLoc)
  have hC3x : ∀ j, C3.x j = C''.x j := fun j => by
    have := hC3.x j; simpa [Fin.castLE_refl] using this
  have heq : ∀ J' : MC (PolyLoc S) (n + 1), J'.Adm It → J'.e = Et → ∀ v,
      J'.RF v = C''.RF Et v := by
    intro J' hJ' he v
    have h := (hbound J' (by rwa [Ideal.map_id])).2 (by rw [pad_refl]; exact he) v
    rw [h, pad_refl]
    exact Chart.RF_congr (fun j _ => hC3x j) v
  have hEt : Et = nextE (pad (n + 1) ek) k (1 / N) := by rw [hEtdef, hW]
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap ⟨k, hk1⟩ (Fin.last n) with hσdef
  have hEtσ : ∀ a : Fin n, Et (σ (Fin.castSucc a)) = ek a := fun a => by
    rw [hEt]; exact nextE_pad_swap hk1 hz _ a
  have hEtk : Et ⟨k, hk1⟩ = 1 / N := by rw [hEt]; exact nextE_pad_at hk1 _
  have hlamEt : ∀ α : Fin (n + 1) →₀ ℕ, lam Et α =
      lam ek (Finsupp.equivFunOnFinite.symm fun a => α (σ (Fin.castSucc a))) +
        α ⟨k, hk1⟩ * (1 / N) := by
    intro α
    rw [lam, sum_swap_last hk1, lam]
    simp only [Finsupp.coe_equivFunOnFinite_symm, hEtσ, hEtk, ← hσdef]
  -- Step 4: the flowed centre
  set y : Fin n → PolyLoc S := fun a => flowN δ N (ck.x a) with hydef
  have hy : ∀ a, ∃ h, y a = ψ (ck.x a) + t * h := fun a =>
    ⟨_, by simp only [hydef, hNdef]; exact flowN_succ δ d (ck.x a)⟩
  set z : Fin (n + 1) → PolyLoc S := Fin.lastCases t y with hzdef
  have hzunit := flow_jac_isUnit ck y hy
  set cz := C.change z hzunit with hczdef
  have hcz : cz.IsCentred :=
    Chart.IsCentred.change' (Chart.polyLoc_isCentred ck hck) z hzunit (flow_span_eq ck y hy)
  have hczx : cz.x (Fin.last n) = t := by simp [hczdef, hzdef]
  have hczd : cz.d (Fin.last n) t = 1 := by rw [← hczx, cz.d_x]; simp
  have hu2 : cz.d (Fin.last n) ((N : PolyLoc S) * t) = ↑u := by
    rw [Derivation.leibniz, hczd, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul,
      mul_one, hudef, IsUnit.unit_spec]
  set J2c := nextChart cz ⟨k, hk1⟩ (Fin.last n) ((N : PolyLoc S) * t) u hu2 with hJ2cdef
  have hNtm : (N : PolyLoc S) * t ∈ maximalIdeal (PolyLoc S) :=
    Ideal.mul_mem_left _ _ polyT_mem_maximal
  have hJ2c : J2c.IsCentred := (hcz.replace (Fin.last n) _ u hu2 hNtm).reindex _
  have hNinvq : (0 : ℚ) ≤ 1 / N := by positivity
  have hEt_nn : ∀ j, 0 ≤ Et j := fun j => by
    rw [hEt]; simp only [nextE]; split_ifs
    · simp only [pad]; split_ifs
      · exact hnn _
      · exact le_rfl
    · exact hNinvq
    · exact le_rfl
  have hbk : ∀ a : Fin n, (a : ℕ) < k → (1 : ℚ) / N ≤ ek a := fun a ha => by
    refine le_trans ?_ (hpos a ha)
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    rw [hNdef]; push_cast
    exact one_div_le_one_div_of_le hdq (by linarith)
  have hEt_anti : Antitone Et := by
    rw [hEt]; exact nextE_pad_antitone hnn hanti hkn hNinvq hbk
  -- `tᴺ` has weight `1`
  have hJ2xk : J2c.x ⟨k, hk1⟩ = (N : PolyLoc S) * t := by
    simp only [hJ2cdef, nextChart, Chart.reindex_x, Equiv.swap_apply_left, Chart.replace_x_self]
  have htN_RF : t ^ N ∈ J2c.RF Et 1 := by
    have h1 : (N : PolyLoc S) * t ∈ J2c.RF Et (1 / N) := by
      rw [← hJ2xk, ← hEtk]; exact J2c.x_mem_RF Et _ (by rw [hEtk]; positivity)
    have h2 := J2c.pow_mem_RF Et h1 N
    rw [show ((N : ℕ) : ℚ) * (1 / N) = 1 by field_simp] at h2
    have : t ^ N = ((u⁻¹ : (PolyLoc S)ˣ) : PolyLoc S) ^ N * ((N : PolyLoc S) * t) ^ N := by
      rw [← mul_pow, ← mul_assoc, show (N : PolyLoc S) = ↑u from (IsUnit.unit_spec _).symm,
        Units.inv_mul, one_mul]
    rw [this]; exact Ideal.mul_mem_left _ _ h2
  -- Claim A: the flow maps weighted ideals into those of the flowed chart
  have hΦx : ∀ a, flowHom δ N hN (ck.x a) = Ideal.Quotient.mk (Ideal.span {t ^ N}) (y a) :=
    fun a => rfl
  have hczxa : ∀ a : Fin n, cz.x (Fin.castSucc a) = y a := fun a => by simp [hczdef, hzdef]
  have hmono : ∀ α : Fin n →₀ ℕ, (∀ a, ek a = 0 → α a = 0) → ∀ v, v ≤ lam ek α →
      ∏ a, y a ^ α a ∈ J2c.RF Et v := by
    intro α hα0 v hv
    set α' : Fin (n + 1) →₀ ℕ := Finsupp.equivMapDomain σ (pushIdx (Nat.le_succ n) α) with hα'def
    have hα'σ : ∀ a, α' (σ (Fin.castSucc a)) = α a := fun a => by
      rw [hα'def, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, ← castLE_succ_eq,
        pushIdx_apply]
    have hα'k : α' ⟨k, hk1⟩ = 0 := by
      rw [hα'def, Finsupp.equivMapDomain_apply, hσdef, Equiv.symm_swap, Equiv.swap_apply_left]
      exact pushIdx_apply_ge _ _ _ (by simp)
    have hprod : ∏ j, J2c.x j ^ α' j = ∏ a, y a ^ α a := by
      rw [hJ2cdef, prod_nextChart_last cz hk1 _ u hu2 α', hα'k, pow_zero, mul_one]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← hσdef, hα'σ, hczxa]
    rw [← hprod]
    refine Ideal.subset_span ⟨α', fun j hj => ?_, ?_, rfl⟩
    · obtain ⟨j', rfl⟩ : ∃ j', σ j' = j := ⟨σ.symm j, by simp⟩
      rw [hα'def, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
      cases j' using Fin.lastCases with
      | last => exact pushIdx_apply_ge _ _ _ (by simp)
      | cast a =>
        rw [← castLE_succ_eq, pushIdx_apply]
        exact hα0 a (by rw [← hEtσ a]; exact hj)
    · rw [hlamEt, hα'k]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      convert hv using 2
      ext a; simp [hα'σ]
  have hclaimA : ∀ v ≤ (1 : ℚ), ∀ f ∈ ck.RF ek v, flowN δ N f ∈ J2c.RF Et v := by
    intro v hv f hf
    have hmap : Ideal.map (flowHom δ N hN) (ck.RF ek v) ≤
        Ideal.map (Ideal.Quotient.mk (Ideal.span {t ^ N})) (J2c.RF Et v) := by
      rw [Chart.RF, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨α, hα0, hαv, rfl⟩, rfl⟩
      have : flowHom δ N hN (∏ a, ck.x a ^ α a) =
          Ideal.Quotient.mk (Ideal.span {t ^ N}) (∏ a, y a ^ α a) := by
        simp only [map_prod, map_pow, hΦx]
      rw [SetLike.mem_coe, this]
      exact Ideal.mem_map_of_mem _ (hmono α hα0 v hαv)
    have h1 := hmap (Ideal.mem_map_of_mem _ hf)
    rw [flowHom_apply, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h1
    have hle : J2c.RF Et v ⊔ Ideal.span {t ^ N} ≤ J2c.RF Et v := sup_le le_rfl (by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact J2c.RF_antitone Et hv htN_RF)
    exact hle h1
  -- Claim B: `ψ(I)` is admissible for the flowed centre
  have hiter : ∀ m, ∀ f ∈ I, δ^[m] f ∈ I := by
    intro m
    induction m with
    | zero => intro f hf; exact hf
    | succ m ih => intro f hf; rw [Function.iterate_succ_apply']; exact hδ _ (ih f hf)
  have hclaimB : I.map ψ ≤ J2c.RF Et 1 := by
    have key : ∀ r : ℕ, I.map ψ ≤ J2c.RF Et 1 ⊔ Ideal.span {t ^ r} * I.map ψ := by
      intro r
      induction r with
      | zero =>
        rw [pow_zero, Ideal.span_singleton_one, Ideal.top_mul]; exact le_sup_right
      | succ r ih =>
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        rw [Ideal.mem_comap]
        have hflow := flowN_succ δ d f
        rw [← hNdef] at hflow
        set sumT := ∑ m ∈ Finset.range d,
          toPolyLoc (((m + 1).factorial : ℚ)⁻¹ • δ^[m + 1] f) * polyT ^ m with hsumTdef
        have hsum : sumT ∈ I.map ψ := Ideal.sum_mem _ fun m _ =>
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem ψ
            (Submodule.smul_of_tower_mem I _ (hiter (m + 1) f hf)))
        have hA : flowN δ N f ∈ J2c.RF Et 1 := hclaimA 1 le_rfl f (hadm hf)
        have hψf : ψ f = flowN δ N f - t * sumT := by rw [hflow]; ring
        rw [hψf]
        refine Ideal.sub_mem _ (Ideal.mem_sup_left hA) ?_
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (ih hsum)
        rw [← hab, mul_add]
        refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ ha))
          (Ideal.mem_sup_right ?_)
        rw [pow_succ', ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
        exact Ideal.mul_mem_mul (Ideal.subset_span rfl) hb
    have hN' : Ideal.span {t ^ N} * I.map ψ ≤ J2c.RF Et 1 := by
      refine le_trans Ideal.mul_le_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact htN_RF
    exact (key N).trans (sup_le le_rfl hN')
  -- the flowed centre is admissible, hence has the same weighted ideals as the run
  have hadm2 : It ≤ J2c.RF Et 1 :=
    sup_le hclaimB (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact htN_RF)
  have hRF := heq ⟨J2c, Et, hJ2c, hEt_nn, hEt_anti⟩ hadm2 rfl
  have hi1 : Fin.castSucc i ≠ ⟨k, hk1⟩ := fun h => by
    have := congrArg Fin.val h; simp at this; omega
  have hi2 : Fin.castSucc i ≠ Fin.last n := (Fin.castSucc_lt_last i).ne
  have hJ2x : J2c.x (Fin.castSucc i) = y i := by
    simp only [hJ2cdef, nextChart, Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne hi1 hi2]
    rw [Chart.replace_x_ne _ _ _ _ _ hi2, hczxa]
  have hEti : Et (Fin.castSucc i) = ek i := by
    have := hEtσ i
    rwa [hσdef, Equiv.swap_apply_of_ne_of_ne hi1 hi2] at this
  have hyi : y i ∈ C''.RF Et (ek i) := by
    have h1 : y i ∈ J2c.RF Et (Et (Fin.castSucc i)) := by
      rw [← hJ2x]; exact J2c.x_mem_RF Et _ (by rw [hEti]; exact (hsupp i).2 hi)
    rw [hEti] at h1
    have h2 := hRF (ek i)
    exact h2 ▸ h1
  -- extraction of the `t`-coefficient
  have hgen : ∀ g ∈ {f | ∃ α : Fin (n + 1) →₀ ℕ, (∀ j, Et j = 0 → α j = 0) ∧ ek i ≤ lam Et α ∧
      f = ∏ j, C''.x j ^ α j},
      (dualLoc g).fst ∈ ck.RF ek (ek i) ∧ (dualLoc g).snd ∈ ck.RF ek (ek i - 1 / N) := by
    rintro _ ⟨α, hα0, hαv, rfl⟩
    set β' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => α (σ (Fin.castSucc a))
      with hβ'def
    have hβ'0 : ∀ a, ek a = 0 → β' a = 0 := fun a ha => by
      simp only [hβ'def, Finsupp.coe_equivFunOnFinite_symm]
      exact hα0 _ (by rw [hEtσ]; exact ha)
    have hlamβ := hlamEt α
    rw [hC''def, prod_nextChart_last C hk1 _ u hu α, hDv, map_mul, map_prod, map_pow]
    have hP : (∏ a : Fin n, dualLoc (C.x (Fin.castSucc a) ^ α (σ (Fin.castSucc a)))) =
        inl (∏ a, ck.x a ^ β' a) := by
      rw [← inlHom_apply, map_prod]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [map_pow, Chart.polyLoc_x_castSucc, dualLoc_toPolyLoc, hβ'def,
        Finsupp.coe_equivFunOnFinite_symm, map_pow]
      rfl
    have hNt : dualLoc ((N : PolyLoc S) * t) = inr (N : S) := by
      rw [map_mul, map_natCast, dualLoc_polyT, ← inl_natCast, inl_mul_inr, smul_eq_mul, mul_one]
    rw [← hσdef, hP, hNt]
    have hmem0 : ∀ v, v ≤ lam ek β' → ∏ a, ck.x a ^ β' a ∈ ck.RF ek v := fun v hv =>
      Ideal.subset_span ⟨β', hβ'0, hv, rfl⟩
    rcases Nat.lt_or_ge (α ⟨k, hk1⟩) 2 with hm | hm
    · interval_cases hmk : α ⟨k, hk1⟩
      · rw [pow_zero, mul_one]
        simp only [fst_inl, snd_inl]
        refine ⟨hmem0 _ ?_, zero_mem _⟩
        have h0 : lam ek β' = lam Et α := by rw [hlamβ, hβ'def]; simp
        linarith
      · rw [pow_one, inl_mul_inr]
        simp only [fst_inr, snd_inr, smul_eq_mul]
        refine ⟨zero_mem _, Ideal.mul_mem_right _ _ (hmem0 _ ?_)⟩
        have h1 : lam ek β' = lam Et α - 1 / N := by rw [hlamβ, hβ'def]; push_cast; ring
        linarith
    · obtain ⟨m, hm'⟩ : ∃ m, α ⟨k, hk1⟩ = m + 2 := ⟨α ⟨k, hk1⟩ - 2, by omega⟩
      rw [hm', pow_add, pow_two, inr_mul_inr, mul_zero, mul_zero]
      simp
  have hext := dualLoc_span (ck.RF_antitone ek (by
    have : (0 : ℚ) ≤ 1 / N := hNinvq; linarith)) hgen (y i) hyi
  rw [hydef] at hext
  simp only at hext
  rw [dualLoc_flowN δ hN2] at hext
  simp only [snd_add, snd_inl, snd_inr, zero_add] at hext
  -- discreteness of the weights
  have hdisc : ck.RF ek (ek i - 1 / N) ≤ ck.RF ek (ek i) := by
    apply Ideal.span_mono
    rintro _ ⟨α, hα0, hαv, rfl⟩
    refine ⟨α, hα0, ?_, rfl⟩
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hlamw : (d : ℚ) * lam ek α = ((∑ j, α j * w j : ℕ) : ℚ) := by
      rw [lam, Finset.mul_sum]; push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw j]; ring
    have hwi : (d : ℚ) * ek i = w i := (hw i).symm
    have h1 : (w i : ℚ) - d / N ≤ ((∑ j, α j * w j : ℕ) : ℚ) := by
      rw [← hwi, ← hlamw]
      have := mul_le_mul_of_nonneg_left hαv hdq.le
      calc (d : ℚ) * ek i - d / N = d * (ek i - 1 / N) := by ring
        _ ≤ d * lam ek α := this
    have h2 : (d : ℚ) / N < 1 := by
      rw [div_lt_one (by positivity)]; rw [hNdef]; push_cast; linarith
    have h3 : w i ≤ ∑ j, α j * w j := by
      have : (w i : ℚ) < ((∑ j, α j * w j : ℕ) : ℚ) + 1 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have h4 : (d : ℚ) * ek i ≤ d * lam ek α := by
      rw [hwi, hlamw]; exact_mod_cast h3
    exact le_of_mul_le_mul_left h4 hdq
  exact hdisc hext.2

end K

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing

section Length

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [IsNoetherianRing S] {n : ℕ}

/-- **Length bound.** If `I` is stable under `m` derivations that are independent at the closed
point, the maximal centre of `I` has at most `n - m` coordinates. -/
theorem length_le_of_derivations {I : Ideal S} {c : Chart S n} {k : ℕ} {ck : Chart S n}
    {ek : Fin n → ℚ} (hrun : IsRun I 0 c 0 k ck ek) (hadm : I ≤ ck.RF ek 1) (hck : ck.IsCentred)
    (hnn : ∀ i, 0 ≤ ek i) (hanti : Antitone ek) (hsupp : ∀ i, ek i ≠ 0 ↔ (i : ℕ) < k)
    {m : ℕ} (δ : Fin m → Derivation ℚ S S) (hδ : ∀ j, ∀ f ∈ I, δ j f ∈ I) (y : Fin m → S)
    (hy : IsUnit (Matrix.of fun j l => δ j (y l)).det) : k + m ≤ n := by
  classical
  have hkn : k ≤ n := hrun.stage_le (Nat.zero_le _)
  -- `δ_j` maps the centre coordinates into `𝔪`
  have hmem : ∀ j, ∀ i : Fin n, (i : ℕ) < k → δ j (ck.x i) ∈ maximalIdeal S := by
    intro j i hi
    have h := deriv_mem_RF hrun hadm hck hnn hanti hsupp (δ j) (hδ j) i hi
    exact hck.RF_le_maximalIdeal (lt_of_le_of_ne (hnn i) (Ne.symm ((hsupp i).2 hi))) h
  set T := {i : Fin n // k ≤ (i : ℕ)}
  set A : Matrix (Fin m) T (ResidueField S) := Matrix.of fun j t => residue S (δ j (ck.x t.1))
  set B : Matrix T (Fin m) (ResidueField S) := Matrix.of fun t l => residue S (ck.d t.1 (y l))
  have hM : (residue S).mapMatrix (Matrix.of fun j l => δ j (y l)) = A * B := by
    ext j l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B]
    have h1 : δ j (y l) = ∑ i, δ j (ck.x i) * ck.d i (y l) := by
      conv_lhs => rw [ck.eq_sum (δ j)]
      rw [Derivation.sum_apply']
      simp only [Derivation.smul_apply, smul_eq_mul]
    rw [h1, map_sum]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => k ≤ (i : ℕ))]
    have h2 : ∑ i : {i : Fin n // ¬ k ≤ (i : ℕ)}, residue S (δ j (ck.x i.1) * ck.d i.1 (y l)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [map_mul, (residue_eq_zero_iff _).2 (hmem j i.1 (by have := i.2; omega)), zero_mul]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
  have hdet : IsUnit (A * B).det := by
    rw [← hM, ← RingHom.map_det]
    exact hy.map _
  have hrank : (A * B).rank = m := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hdet), Fintype.card_fin]
  have hle : (A * B).rank ≤ Fintype.card T := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  have hcard : Fintype.card T = n - k := by
    rw [Fintype.card_subtype, ← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
    have : (Finset.univ.filter fun i : Fin n => k ≤ (i : ℕ)).map ⟨Fin.val, Fin.val_injective⟩ =
        Finset.Ico k n := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk, Finset.mem_Ico]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
    rw [this, Nat.card_Ico]
  omega

end Length

end BezoutCounterexample.Principalization

