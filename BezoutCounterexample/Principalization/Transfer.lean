import BezoutCounterexample.Principalization.Centre

/-!
# Method-1 runs and the transfer theorem

A *run* (`IsRun`) records the choices of Method 1: at each stage a witness `f ∈ I`, a
multi-index `β` minimizing `Ξ`, and the new parameter `∂^{β - e_l} f`.  Runs exist for every
nonzero ideal in `𝔪` (`MC.exists_run`), and can be transported along any ring homomorphism
`ψ : S → R'` to a local ring with a compatible chart: `IsRun.transfer_bound` bounds all
admissible marked centres of `I R'` lexicographically from below by the weights of the run and
identifies those with equal weights.  This gives upper semicontinuity of the invariant and its
invariance under smooth base change (Theorem 3.3 (2), (3) of the paper).
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}

/-- The weights after a Method-1 step. -/
def nextE (e : Fin n → ℚ) (j : ℕ) (b : ℚ) : Fin n → ℚ :=
  fun i => if (i : ℕ) < j then e i else if (i : ℕ) = j then b else 0

/-- The chart after a Method-1 step: replace `x_l` by `g` and move it to position `jj`. -/
def nextChart (c : Chart S n) (jj l : Fin n) (g : S) (u : Sˣ) (hu : c.d l g = u) : Chart S n :=
  (c.replace l g u hu).reindex (Equiv.swap jj l)

/-- The next weight of a Method-1 step. -/
def nextW (e : Fin n → ℚ) (j : ℕ) (β : Fin n →₀ ℕ) : ℚ := (1 - lam e β) / tailSum j β

/-- **Method-1 runs** (certificates): a sequence of Method-1 steps from stage `j` (chart `c`,
weights `e`) to stage `k` (chart `ck`, weights `ek`). -/
inductive IsRun (I : Ideal S) :
    ℕ → Chart S n → (Fin n → ℚ) → ℕ → Chart S n → (Fin n → ℚ) → Prop
  | refl (j : ℕ) (c : Chart S n) (e : Fin n → ℚ) : IsRun I j c e j c e
  | step {j : ℕ} {c : Chart S n} {e : Fin n → ℚ} {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ}
      (hj : j < n) (f : S) (hf : f ∈ I) (β : Fin n →₀ ℕ) (l : Fin n) (hl : j ≤ (l : ℕ))
      (hβl : β l ≠ 0) (hlam : lam e β < 1) (hN : 0 < tailSum j β) (hunit : IsUnit (c.D β f))
      (hb : ∀ i : Fin n, (i : ℕ) < j → nextW e j β ≤ e i)
      (u : Sˣ) (hu : c.d l (c.Dv (β - Finsupp.single l 1) f) = u)
      (hnext : IsRun I (j + 1) (nextChart c ⟨j, hj⟩ l (c.Dv (β - Finsupp.single l 1) f) u hu)
        (nextE e j (nextW e j β)) k ck ek) : IsRun I j c e k ck ek

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

namespace MC

variable {I : Ideal R} {j : ℕ} {J : MC R n}

theorem SA.step_run (hSA : SA I j J) (hna : ¬ J.Adm I) :
    ∃ (hj : j < n) (f : R) (_ : f ∈ I) (β : Fin n →₀ ℕ) (l : Fin n) (_ : j ≤ (l : ℕ))
      (_ : β l ≠ 0) (_ : lam J.e β < 1) (_ : 0 < tailSum j β) (_ : IsUnit (J.c.D β f))
      (_ : ∀ i : Fin n, (i : ℕ) < j → nextW J.e j β ≤ J.e i)
      (u : Rˣ) (hu : J.c.d l (J.c.Dv (β - Finsupp.single l 1) f) = u)
      (hc : (nextChart J.c ⟨j, hj⟩ l (J.c.Dv (β - Finsupp.single l 1) f) u hu).IsCentred)
      (hnn : ∀ i, 0 ≤ nextE J.e j (nextW J.e j β) i)
      (ha : Antitone (nextE J.e j (nextW J.e j β))),
      SA I (j + 1) ⟨nextChart J.c ⟨j, hj⟩ l (J.c.Dv (β - Finsupp.single l 1) f) u hu,
        nextE J.e j (nextW J.e j β), hc, hnn, ha⟩ := by
  classical
  obtain ⟨hj, βs, f, hf, hfne, hlt, hN, hmin, hnext, hbJ⟩ := hSA.step_data hna
  set jj : Fin n := ⟨j, hj⟩ with hjj
  set bp : ℚ := (1 - lam J.e βs) / tailSum j βs with hbpdef
  have hNq : (0 : ℚ) < tailSum j βs := by exact_mod_cast hN
  have hbp : 0 < bp := div_pos (by linarith) hNq
  have hzero : ∀ i : Fin n, j ≤ (i : ℕ) → J.e i = 0 := fun i hi => hSA.e_eq_zero hi
  have hkey : lam J.e βs + bp * tailSum j βs = 1 := by
    rw [hbpdef]; field_simp; ring
  have hS_bound : ∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) → lam J.e β < 1 →
      1 ≤ lam J.e β + bp * tailSum j β := by
    intro β hβ hβlt
    have hX := hmin β hβ hβlt
    simp only [Xi] at hX
    have h1 : 0 < 1 - lam J.e β := by linarith
    have h2 : 0 < 1 - lam J.e βs := by linarith
    rw [div_le_div_iff₀ h2 h1] at hX
    have : 1 - lam J.e β ≤ bp * tailSum j β := by
      rw [hbpdef, div_mul_eq_mul_div, le_div_iff₀ hNq]; linarith
    linarith
  -- the completion is an admissible marked centre
  have hc_nonneg : ∀ i, 0 ≤ compl J.e j bp i := fun i => by
    simp only [compl]; split_ifs
    · exact J.nonneg i
    · exact hbp.le
  have hc_anti : Antitone (compl J.e j bp) := by
    intro i i' hii'
    simp only [compl]
    by_cases h1 : (i' : ℕ) < j
    · have h2 : (i : ℕ) < j := lt_of_le_of_lt (Fin.le_def.1 hii') h1
      rw [ite_eq_left h1, ite_eq_left h2]; exact J.anti hii'
    · rw [ite_eq_right h1]
      by_cases h2 : (i : ℕ) < j
      · rw [ite_eq_left h2]; exact hbJ i h2
      · rw [ite_eq_right h2]
  have hc_adm : I ≤ J.c.RF (compl J.e j bp) 1 := by
    intro g hg
    rw [J.centred.mem_RF_iff hc_nonneg]
    intro β hβ
    by_contra hne
    rw [lam_compl hzero] at hβ
    by_cases hβ1 : lam J.e β < 1
    · have := hS_bound β ⟨g, hg, hne⟩ hβ1; linarith
    · have : 0 ≤ bp * tailSum j β := mul_nonneg hbp.le (Nat.cast_nonneg _)
      linarith
  -- the new parameter
  obtain ⟨l, hl, hβl⟩ := tailSum_pos_exists hN
  set γ := βs - Finsupp.single l 1 with hγdef
  have hγ : γ + Finsupp.single l 1 = βs := add_single_sub hβl
  have hlamγ : lam J.e γ = lam J.e βs := by
    rw [← hγ, lam_add, lam_single, hzero l hl, mul_zero, add_zero]
  have htailγ : tailSum j γ + 1 = tailSum j βs := tailSum_sub_single hl hβl
  set xb := J.c.Dv γ f with hxb
  have hdl : J.c.d l xb = ((γ l + 1 : ℕ) : ℚ) • J.c.Dv βs f := by rw [hxb, Chart.d_Dv, hγ]
  have hdl_nm : J.c.d l xb ∉ maximalIdeal R := by
    intro hmem
    rw [hdl, ← residue_eq_zero_iff, map_rat_smul] at hmem
    rw [← Chart.coeff_tau] at hmem
    exact hfne ((smul_eq_zero.1 hmem).resolve_left (by positivity))
  have hxb_mem : xb ∈ maximalIdeal R := by
    rw [hxb, ← residue_eq_zero_iff, ← Chart.coeff_tau]
    by_contra hne
    have hX := hmin γ ⟨f, hf, hne⟩ (by rw [hlamγ]; exact hlt)
    simp only [Xi, hlamγ] at hX
    have h2 : 0 < 1 - lam J.e βs := by linarith
    rw [div_le_div_iff_of_pos_right h2] at hX
    have : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j βs := by exact_mod_cast htailγ
    linarith
  obtain ⟨u, hu⟩ := notMem_maximalIdeal.1 hdl_nm
  -- the new chart and weights
  set cp := (J.c.replace l xb u hu.symm).reindex (Equiv.swap jj l) with hcp
  have hcp_centred : cp.IsCentred := (J.centred.replace l xb u hu.symm hxb_mem).reindex _
  set ep : Fin n → ℚ := fun i => if (i : ℕ) < j then J.e i else if (i : ℕ) = j then bp else 0
    with hep
  have hep_nonneg : ∀ i, 0 ≤ ep i := fun i => by
    simp only [hep]; split_ifs
    · exact J.nonneg i
    · exact hbp.le
    · exact le_rfl
  have hep_anti : Antitone ep := by
    intro i i' hii'
    have hle := Fin.le_def.1 hii'
    simp only [hep]
    by_cases h1 : (i' : ℕ) < j
    · rw [ite_eq_left h1, ite_eq_left (lt_of_le_of_lt hle h1)]; exact J.anti hii'
    · rw [ite_eq_right h1]
      by_cases h2 : (i' : ℕ) = j
      · rw [ite_eq_left h2]
        by_cases h3 : (i : ℕ) < j
        · rw [ite_eq_left h3]; exact hbJ i h3
        · rw [ite_eq_right h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h2]
        split_ifs
        · exact J.nonneg i
        · exact hbp.le
        · exact le_rfl
  have hcp_x_lt : ∀ i : Fin n, (i : ℕ) < j → cp.x i = J.c.x i := by
    intro i hi
    have h1 : i ≠ jj := fun h => by rw [h] at hi; simp [hjj] at hi
    have h2 : i ≠ l := fun h => by rw [h] at hi; omega
    rw [hcp, Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne h1 h2, J.c.replace_x_ne _ _ _ _ h2]
  have hcp_x_j : cp.x jj = xb := by
    rw [hcp, Chart.reindex_x, Equiv.swap_apply_left, J.c.replace_x_self]
  have hunitD : IsUnit (J.c.D βs f) := by
    rw [← notMem_maximalIdeal]
    intro hmem
    apply hfne
    rw [Chart.coeff_tau, residue_eq_zero_iff, Chart.Dv, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hmem
  refine ⟨hj, f, hf, βs, l, hl, hβl, hlt, hN, hunitD, hbJ, u, hu.symm, hcp_centred, hep_nonneg,
    hep_anti, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- support
    intro i
    show ep i ≠ 0 ↔ (i : ℕ) < j + 1
    simp only [hep]
    by_cases h1 : (i : ℕ) < j
    · rw [ite_eq_left h1]; exact ⟨fun _ => by omega, fun _ => (hSA.supp i).2 h1⟩
    · rw [ite_eq_right h1]
      by_cases h2 : (i : ℕ) = j
      · rw [ite_eq_left h2]; exact ⟨fun _ => by omega, fun _ => hbp.ne'⟩
      · rw [ite_eq_right h2]; exact ⟨fun h => absurd rfl h, fun h => by omega⟩
  · -- domination by an admissible centre: the completion
    refine ⟨⟨J.c, compl J.e j bp, J.centred, hc_nonneg, hc_anti⟩, hc_adm, fun i hi => ?_⟩
    show compl J.e j bp i = ep i
    simp only [compl, hep]
    by_cases h1 : (i : ℕ) < j
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left (by omega)]
  · -- maximality
    intro J' hJ' i hi hbelow
    by_cases h1 : (i : ℕ) < j
    · have : ep i = J.e i := by simp only [hep, ite_eq_left h1]
      show ep i ≤ J'.e i
      rw [this]
      refine hSA.max J' hJ' i h1 fun i' hi' => ?_
      rw [hbelow i' hi']
      show ep i' = J.e i'
      simp only [hep, ite_eq_left (lt_trans (Fin.lt_def.1 hi') h1)]
    · have hij : (i : ℕ) = j := by omega
      have hieq : i = jj := Fin.ext hij
      subst hieq
      have hag : ∀ i' : Fin n, (i' : ℕ) < j → J'.e i' = J.e i' := fun i' hi' => by
        rw [hbelow i' (Fin.lt_def.2 hi')]
        show ep i' = J.e i'
        simp only [hep, ite_eq_left hi']
      have := (hnext J' hJ' hag).2
      show ep jj ≤ J'.e jj
      simp only [hep, ite_eq_right h1, ite_eq_left hij]
      exact this
  · -- domination
    intro J' hJ' hag
    have hag_j : ∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i := fun i hi => by
      rw [hag i (by omega)]; show ep i = J.e i; simp only [hep, ite_eq_left hi]
    have hJ'j : J'.e jj = bp := by
      rw [hag jj (by simp [hjj])]; show ep jj = bp; simp [hep, hjj]
    obtain ⟨c'', hc'', hRF, hx⟩ := hSA.dom J' hJ' hag_j
    have hf' : f ∈ c''.RF J'.e 1 := by rw [hRF]; exact hJ' hf
    -- lowering bounds for the derivations of `J.c` with respect to `(c'', J'.e)`
    have hlow : ∀ i, c''.LowersBy J'.e (J.c.d i) (compl J.e j bp i) := by
      intro i
      by_cases hi : (i : ℕ) < j
      · have := hc''.lowersBy_lt (c := J.c) J'.nonneg J'.anti (fun i' hi' => (hx i' hi').symm) i hi
        simp only [compl, ite_eq_left hi]
        rwa [hag_j i hi] at this
      · simp only [compl, ite_eq_right hi]
        refine hc''.lowersBy_ge (c := J.c) J'.nonneg (fun i' hi' => (hx i' hi').symm) i (by omega)
          fun m hm => ?_
        rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by simp only [hjj, Fin.val_mk]; omega))
    have hxb_RF : xb ∈ c''.RF J'.e bp := by
      have hm1 := Chart.Dv_mem_RF_of_lowersBy c'' J.c J'.e (compl J.e j bp) hlow γ hf'
      rw [lam_compl hzero, hlamγ] at hm1
      have htq : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j βs := by exact_mod_cast htailγ
      have hm2 : 1 - (lam J.e βs + bp * (tailSum j γ : ℚ)) = bp := by
        have := hkey; rw [← htq] at this; linarith
      rw [hm2] at hm1
      exact hm1
    -- a coordinate of `c''` in which `xb` has a linear term
    obtain ⟨m, hm, hmnm⟩ : ∃ m : Fin n, j ≤ (m : ℕ) ∧ c''.d m xb ∉ maximalIdeal R := by
      by_contra hcon
      push Not at hcon
      apply hdl_nm
      rw [c''.eq_sum (J.c.d l), Derivation.sum_apply']
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [Derivation.smul_apply, smul_eq_mul]
      by_cases hmj : (m : ℕ) < j
      · rw [hx m hmj, J.c.d_x, ite_eq_right (fun h => by rw [h] at hl; omega), zero_mul]
        exact zero_mem _
      · exact Ideal.mul_mem_left _ _ (hcon m (by omega))
    have hJ'm : J'.e m = bp := by
      refine le_antisymm ?_ ?_
      · rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by simp only [hjj, Fin.val_mk]; omega))
      · by_contra hlt'
        push Not at hlt'
        have := (hc''.mem_RF_iff J'.nonneg bp xb).1 hxb_RF (Finsupp.single m 1) (by
          rw [lam_single]; simpa using hlt')
        rw [Chart.coeff_tau_eq_zero_iff, Chart.Dv_single_one] at this
        exact hmnm this
    obtain ⟨u', hu'⟩ := notMem_maximalIdeal.1 hmnm
    refine ⟨(c''.replace m xb u' hu'.symm).reindex (Equiv.swap jj m),
      (hc''.replace m xb u' hu'.symm hxb_mem).reindex _, fun t => ?_, fun i hi => ?_⟩
    · rw [Chart.RF_reindex _ _ (fun i => by
          rcases eq_or_ne i jj with h | h
          · rw [h, Equiv.swap_apply_left, hJ'm, hJ'j]
          · rcases eq_or_ne i m with h' | h'
            · rw [h', Equiv.swap_apply_right, hJ'm, hJ'j]
            · rw [Equiv.swap_apply_of_ne_of_ne h h'])]
      rw [hc''.RF_replace J'.nonneg m xb u' hu'.symm hxb_mem (by rw [hJ'm]; exact hxb_RF), hRF]
    · show ((c''.replace m xb u' hu'.symm).reindex (Equiv.swap jj m)).x i = cp.x i
      by_cases hij : (i : ℕ) < j
      · have h1 : i ≠ jj := fun h => by rw [h] at hij; simp [hjj] at hij
        have h2 : i ≠ m := fun h => by rw [h] at hij; omega
        rw [Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne h1 h2, c''.replace_x_ne _ _ _ _ h2,
          hx i hij, hcp_x_lt i hij]
      · have hieq : i = jj := Fin.ext (by simp [hjj]; omega)
        subst hieq
        rw [Chart.reindex_x, Equiv.swap_apply_left, c''.replace_x_self, hcp_x_j]


end MC

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}

namespace MC

variable {I : Ideal R}

/-- Method 1 produces a run ending in an admissible marked centre. -/
theorem exists_run (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal R) (c : Chart R n) (hc : c.IsCentred) :
    ∃ (k : ℕ) (ck : Chart R n) (ek : Fin n → ℚ), IsRun I 0 c 0 k ck ek ∧ I ≤ ck.RF ek 1 ∧
      ck.IsCentred ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧ (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) := by
  have key : ∀ d j, n - j = d → ∀ J : MC R n, SA I j J →
      ∃ (k : ℕ) (ck : Chart R n) (ek : Fin n → ℚ), IsRun I j J.c J.e k ck ek ∧ I ≤ ck.RF ek 1 ∧
        ck.IsCentred ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧ (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) := by
    intro d
    induction d with
    | zero =>
      intro j hj J hJ
      by_cases ha : J.Adm I
      · exact ⟨j, J.c, J.e, .refl _ _ _, ha, J.centred, J.nonneg, J.anti, hJ.supp⟩
      · obtain ⟨hjn, -⟩ := hJ.step_data ha
        omega
    | succ d ih =>
      intro j hj J hJ
      by_cases ha : J.Adm I
      · exact ⟨j, J.c, J.e, .refl _ _ _, ha, J.centred, J.nonneg, J.anti, hJ.supp⟩
      · obtain ⟨hjn, f, hf, β, l, hl, hβl, hlam, hN, hunit, hb, u, hu, hc', hnn, ha', hSA'⟩ :=
          hJ.step_run ha
        obtain ⟨k, ck, ek, hrun, hadm, hck, hek⟩ := ih (j + 1) (by omega) _ hSA'
        exact ⟨k, ck, ek, .step hjn f hf β l hl hβl hlam hN hunit hb u hu hrun, hadm, hck, hek⟩
  exact key (n - 0) 0 rfl ⟨c, 0, hc, fun _ => le_rfl, fun _ _ _ => le_rfl⟩ (sa_zero hI hIm c hc)

end MC

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] {R' : Type*} [CommRing R'] [Algebra ℚ R']
  {n n' : ℕ} (hnn : n ≤ n')

/-- Padding weights by zeros. -/
def pad (n' : ℕ) (e : Fin n → ℚ) : Fin n' → ℚ := fun i => if h : (i : ℕ) < n then e ⟨i, h⟩ else 0

/-- Pushing multi-indices forward. -/
def pushIdx (β : Fin n →₀ ℕ) : Fin n' →₀ ℕ := Finsupp.mapDomain (Fin.castLE hnn) β

lemma pushIdx_apply (β : Fin n →₀ ℕ) (i : Fin n) : pushIdx hnn β (Fin.castLE hnn i) = β i :=
  Finsupp.mapDomain_apply_of_injective (Fin.castLE_injective hnn) β i

lemma pushIdx_apply_ge (β : Fin n →₀ ℕ) (i : Fin n') (hi : n ≤ (i : ℕ)) : pushIdx hnn β i = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨i', rfl⟩; simp at hi; omega)

lemma pushIdx_add_single (β : Fin n →₀ ℕ) (i : Fin n) :
    pushIdx hnn (β + Finsupp.single i 1) = pushIdx hnn β + Finsupp.single (Fin.castLE hnn i) 1 := by
  simp [pushIdx, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

lemma pad_castLE (e : Fin n → ℚ) (i : Fin n) : pad n' e (Fin.castLE hnn i) = e i := by
  simp [pad]

lemma sum_castLE {M : Type*} [AddCommMonoid M] (g : Fin n' → M) (hg : ∀ i : Fin n', n ≤ (i : ℕ) → g i = 0) :
    ∑ i : Fin n', g i = ∑ i : Fin n, g (Fin.castLE hnn i) := by
  refine (Fintype.sum_of_injective (Fin.castLE hnn) (Fin.castLE_injective hnn) _ g ?_ fun i => rfl).symm
  intro i hi
  refine hg i ?_
  by_contra h
  exact hi ⟨⟨i, by omega⟩, rfl⟩

lemma lam_pad (e : Fin n → ℚ) (β : Fin n →₀ ℕ) : lam (pad n' e) (pushIdx hnn β) = lam e β := by
  rw [lam, sum_castLE hnn _ fun i hi => by simp [pad, show ¬ (i : ℕ) < n by omega]]
  simp only [lam, pushIdx_apply, pad_castLE]

lemma tailSum_push (j : ℕ) (β : Fin n →₀ ℕ) : tailSum j (pushIdx hnn β) = tailSum j β := by
  simp only [tailSum, Finset.sum_filter]
  rw [sum_castLE hnn _ fun i hi => by rw [pushIdx_apply_ge hnn β i hi]; simp]
  simp only [Fin.val_castLE, pushIdx_apply]

lemma fact_push (β : Fin n →₀ ℕ) :
    ∏ i : Fin n', (pushIdx hnn β i).factorial = ∏ i : Fin n, (β i).factorial := by
  refine (Fintype.prod_of_injective (Fin.castLE hnn) (Fin.castLE_injective hnn) _ _ ?_
    fun i => by rw [pushIdx_apply]).symm
  intro i hi
  have : n ≤ (i : ℕ) := by
    by_contra h
    exact hi ⟨⟨i, by omega⟩, rfl⟩
  rw [pushIdx_apply_ge hnn β i this, Nat.factorial_zero]

/-- A chart `c'` on `R'` extends a chart `c` on `S` along `ψ : S → R'`. -/
structure Compat (ψ : S →+* R') (c : Chart S n) (c' : Chart R' n') : Prop where
  x : ∀ i : Fin n, c'.x (Fin.castLE hnn i) = ψ (c.x i)
  d : ∀ (i : Fin n) (f : S), c'.d (Fin.castLE hnn i) (ψ f) = ψ (c.d i f)
  d_extra : ∀ i : Fin n', n ≤ (i : ℕ) → ∀ f : S, c'.d i (ψ f) = 0

variable {hnn}

lemma Compat.D {ψ : S →+* R'} {c : Chart S n} {c' : Chart R' n'} (h : Compat hnn ψ c c')
    (β : Fin n →₀ ℕ) (f : S) : c'.D (pushIdx hnn β) (ψ f) = ψ (c.D β f) := by
  revert f
  refine Finsupp.induction_single (P := fun β => ∀ f, c'.D (pushIdx hnn β) (ψ f) = ψ (c.D β f))
    ?_ ?_ β
  · intro f; simp [pushIdx, Chart.D_zero]
  · intro β i ih f
    rw [pushIdx_add_single, Chart.D_add_single, ih, h.d, Chart.D_add_single]

lemma Compat.Dv {ψ : S →+* R'} {c : Chart S n} {c' : Chart R' n'} (h : Compat hnn ψ c c')
    (β : Fin n →₀ ℕ) (f : S) : c'.Dv (pushIdx hnn β) (ψ f) = ψ (c.Dv β f) := by
  rw [Chart.Dv, Chart.Dv, h.D, fact_push, map_rat_smul]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] {R' : Type*} [CommRing R'] [Algebra ℚ R']
  {n n' : ℕ} {hnn : n ≤ n'}

lemma swap_castLE (hnn : n ≤ n') (a b i : Fin n) :
    Equiv.swap (Fin.castLE hnn a) (Fin.castLE hnn b) (Fin.castLE hnn i) =
      Fin.castLE hnn (Equiv.swap a b i) := by
  have hinj := Fin.castLE_injective hnn
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  by_cases h1 : i = a
  · subst h1; simp
  · by_cases h2 : i = b
    · subst h2; simp [h1]
    · rw [ite_eq_right (fun h => h1 (hinj h)), ite_eq_right (fun h => h2 (hinj h)), ite_eq_right h1, ite_eq_right h2]

lemma Compat.hu' {ψ : S →+* R'} {c : Chart S n} {c' : Chart R' n'} (h : Compat hnn ψ c c')
    {l : Fin n} {g : S} {u : Sˣ} (hu : c.d l g = u) :
    c'.d (Fin.castLE hnn l) (ψ g) = ↑(Units.map ψ.toMonoidHom u) := by
  rw [h.d, hu]; rfl

/-- Compatibility is preserved by Method-1 steps. -/
lemma Compat.nextChart {ψ : S →+* R'} {c : Chart S n} {c' : Chart R' n'} (h : Compat hnn ψ c c')
    (jj l : Fin n) (g : S) (u : Sˣ) (hu : c.d l g = u) :
    Compat hnn ψ (nextChart c jj l g u hu)
      (nextChart c' (Fin.castLE hnn jj) (Fin.castLE hnn l) (ψ g) (Units.map ψ.toMonoidHom u)
        (h.hu' hu)) := by
  have hinj := Fin.castLE_injective hnn
  refine ⟨fun i => ?_, fun i f => ?_, fun i hi f => ?_⟩
  · simp only [Principalization.nextChart, Chart.reindex_x, swap_castLE]
    by_cases hm : Equiv.swap jj l i = l
    · rw [hm, Chart.replace_x_self, Chart.replace_x_self]
    · rw [Chart.replace_x_ne _ _ _ _ _ (fun h' => hm (hinj h')), Chart.replace_x_ne _ _ _ _ _ hm, h.x]
  · simp only [Principalization.nextChart, Chart.reindex_d, swap_castLE, Chart.replace]
    by_cases hm : Equiv.swap jj l i = l
    · rw [ite_eq_left (congrArg _ hm), ite_eq_left hm]
      simp only [Derivation.smul_apply, smul_eq_mul, map_mul, h.d]
      rfl
    · rw [ite_eq_right (fun h' => hm (hinj h')), ite_eq_right hm]
      simp only [Derivation.coe_sub, Pi.sub_apply, Derivation.smul_apply, smul_eq_mul, map_sub,
        map_mul, h.d]
      rfl
  · have h1 : i ≠ Fin.castLE hnn jj := fun h' => by rw [h'] at hi; simp at hi; omega
    have h2 : i ≠ Fin.castLE hnn l := fun h' => by rw [h'] at hi; simp at hi; omega
    simp only [Principalization.nextChart, Chart.reindex_d, Equiv.swap_apply_of_ne_of_ne h1 h2,
      Chart.replace, ite_eq_right h2, Derivation.coe_sub, Pi.sub_apply, Derivation.smul_apply,
      smul_eq_mul, h.d_extra i hi, mul_zero, zero_mul, sub_zero]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] {R' : Type*} [CommRing R'] [Algebra ℚ R']
  [IsLocalRing R'] [IsNoetherianRing R'] {n n' : ℕ} {hnn : n ≤ n'}

/-- The transfer invariant at stage `j`: the lexicographic lower bound and the domination
property for admissible marked centres of `I R'`, relative to the run data `(c, e)` on `S`
transported to the chart `c'` on `R'`. -/
structure TI (hnn : n ≤ n') (ψ : S →+* R') (I : Ideal S) (j : ℕ) (c : Chart S n)
    (e : Fin n → ℚ) (c' : Chart R' n') : Prop where
  compat : Compat hnn ψ c c'
  max : ∀ J' : MC R' n', J'.Adm (I.map ψ) → ∀ i : Fin n', (i : ℕ) < j →
    (∀ i' : Fin n', i' < i → J'.e i' = pad n' e i') → pad n' e i ≤ J'.e i
  dom : ∀ J' : MC R' n', J'.Adm (I.map ψ) → (∀ i : Fin n', (i : ℕ) < j → J'.e i = pad n' e i) →
    ∃ c'' : Chart R' n', c''.IsCentred ∧ (∀ t, c''.RF J'.e t = J'.RF t) ∧
      ∀ i : Fin n', (i : ℕ) < j → c''.x i = c'.x i

lemma pad_zero_ge {e : Fin n → ℚ} {j : ℕ} (hsupp : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0)
    (i : Fin n') (hi : j ≤ (i : ℕ)) : pad n' e i = 0 := by
  simp only [pad]; split_ifs with h
  · exact hsupp _ (by simp; omega)
  · rfl

lemma pad_nextE_lt {e : Fin n → ℚ} {j : ℕ} {b : ℚ} (i : Fin n') (hi : (i : ℕ) < j) :
    pad n' (nextE e j b) i = pad n' e i := by
  by_cases h : (i : ℕ) < n
  · simp only [pad, dite_eq_left h, nextE, ite_eq_left hi]
  · simp only [pad, dite_eq_right h]

lemma pad_nextE_eq {e : Fin n → ℚ} {j : ℕ} {b : ℚ} (hj : j < n) (i : Fin n') (hi : (i : ℕ) = j) :
    pad n' (nextE e j b) i = b := by
  have h : (i : ℕ) < n := by omega
  simp only [pad, dite_eq_left h, nextE, ite_eq_right (show ¬ (i : ℕ) < j by omega), ite_eq_left hi]

/-- The bound on the lowering by the derivations of a chart agreeing with `c''` below `j`. -/
lemma lowers_compl {c' c'' : Chart R' n'} (hc'' : c''.IsCentred) {J' : MC R' n'} {j : ℕ}
    {e : Fin n' → ℚ} (hagree : ∀ i : Fin n', (i : ℕ) < j → c''.x i = c'.x i)
    (he : ∀ i : Fin n', (i : ℕ) < j → J'.e i = e i) {b : ℚ}
    (hb : ∀ m : Fin n', j ≤ (m : ℕ) → J'.e m ≤ b) :
    ∀ i, c''.LowersBy J'.e (c'.d i) (compl e j b i) := by
  intro i
  by_cases hi : (i : ℕ) < j
  · have := hc''.lowersBy_lt (c := c') J'.nonneg J'.anti (fun i' hi' => (hagree i' hi').symm) i hi
    simp only [compl, ite_eq_left hi]; rwa [he i hi] at this
  · simp only [compl, ite_eq_right hi]
    exact hc''.lowersBy_ge (c := c') J'.nonneg (fun i' hi' => (hagree i' hi').symm) i (by omega) hb

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] {R' : Type*} [CommRing R'] [Algebra ℚ R']
  [IsLocalRing R'] [IsNoetherianRing R'] {n n' : ℕ} {hnn : n ≤ n'}

lemma lam_compl_pad {e : Fin n → ℚ} {j : ℕ} (hsupp : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0)
    (b : ℚ) (β : Fin n →₀ ℕ) :
    lam (compl (pad n' e) j b) (pushIdx hnn β) = lam e β + b * tailSum j β := by
  rw [lam_compl (pad_zero_ge hsupp), lam_pad, tailSum_push]

/-- **Transfer step.** -/
theorem TI.step {ψ : S →+* R'} {I : Ideal S} {j : ℕ} {c : Chart S n} {e : Fin n → ℚ}
    {c' : Chart R' n'} (hT : TI hnn ψ I j c e c') (hj : j < n)
    (hsupp : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0)
    (f : S) (hf : f ∈ I) (β : Fin n →₀ ℕ) (l : Fin n) (hl : j ≤ (l : ℕ)) (hβl : β l ≠ 0)
    (hlam : lam e β < 1) (hN : 0 < tailSum j β) (hunit : IsUnit (c.D β f))
    (u : Sˣ) (hu : c.d l (c.Dv (β - Finsupp.single l 1) f) = u) :
    TI hnn ψ I (j + 1) (nextChart c ⟨j, hj⟩ l (c.Dv (β - Finsupp.single l 1) f) u hu)
      (nextE e j (nextW e j β))
      (nextChart c' (Fin.castLE hnn ⟨j, hj⟩) (Fin.castLE hnn l)
        (ψ (c.Dv (β - Finsupp.single l 1) f)) (Units.map ψ.toMonoidHom u) (hT.compat.hu' hu)) := by
  classical
  set jj : Fin n := ⟨j, hj⟩ with hjj
  set jj' : Fin n' := Fin.castLE hnn jj with hjj'
  have hjj'v : (jj' : ℕ) = j := by simp [hjj', hjj]
  set b := nextW e j β with hbdef
  have hNq : (0 : ℚ) < tailSum j β := by exact_mod_cast hN
  have hbpos : 0 < b := div_pos (by linarith) hNq
  have hkey : lam e β + b * tailSum j β = 1 := by rw [hbdef, nextW]; field_simp; ring
  set γ := β - Finsupp.single l 1 with hγdef
  have hγ : γ + Finsupp.single l 1 = β := MC.add_single_sub hβl
  have hlamγ : lam e γ = lam e β := by
    rw [← hγ, lam_add, lam_single, hsupp l hl, mul_zero, add_zero]
  have htailγ : tailSum j γ + 1 = tailSum j β := MC.tailSum_sub_single hl hβl
  have hψf : ∀ J' : MC R' n', J'.Adm (I.map ψ) → ψ f ∈ J'.RF 1 :=
    fun J' hJ' => hJ' (Ideal.mem_map_of_mem ψ hf)
  refine ⟨hT.compat.nextChart jj l _ u hu, ?_, ?_⟩
  · -- maximality
    intro J' hJ' i hi hbelow
    by_cases h1 : (i : ℕ) < j
    · rw [pad_nextE_lt i h1]
      exact hT.max J' hJ' i h1 fun i' hi' => by
        rw [hbelow i' hi', pad_nextE_lt i' (lt_trans (Fin.lt_def.1 hi') h1)]
    · have hij : (i : ℕ) = j := by omega
      rw [pad_nextE_eq hj i hij]
      have hag : ∀ i' : Fin n', (i' : ℕ) < j → J'.e i' = pad n' e i' := fun i' hi' => by
        rw [hbelow i' (Fin.lt_def.2 (by omega)), pad_nextE_lt i' hi']
      obtain ⟨c'', hc'', hRF, hx⟩ := hT.dom J' hJ' hag
      by_contra hlt
      push Not at hlt
      have hlow := lowers_compl (c' := c') hc'' hx hag (b := J'.e i) fun m hm =>
        J'.anti (Fin.le_def.2 (by omega))
      have hmem := Chart.D_mem_RF_of_lowersBy c'' c' J'.e _ hlow (pushIdx hnn β) 1 (ψ f)
        (by rw [hRF]; exact hψf J' hJ')
      rw [hT.compat.D, lam_compl_pad hsupp] at hmem
      have hpos : 0 < 1 - (lam e β + J'.e i * tailSum j β) := by
        have : J'.e i * tailSum j β < b * tailSum j β := mul_lt_mul_of_pos_right hlt hNq
        linarith
      have := hc''.RF_le_maximalIdeal hpos hmem
      exact (notMem_maximalIdeal.2 (hunit.map ψ)) this
  · -- domination
    intro J' hJ' hag
    have hag_j : ∀ i : Fin n', (i : ℕ) < j → J'.e i = pad n' e i := fun i hi => by
      rw [hag i (by omega), pad_nextE_lt i hi]
    have hJ'j : J'.e jj' = b := by rw [hag jj' (by omega), pad_nextE_eq hj jj' hjj'v]
    obtain ⟨c'', hc'', hRF, hx⟩ := hT.dom J' hJ' hag_j
    have hlow := lowers_compl (c' := c') hc'' hx hag_j (b := b) fun m hm => by
      rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by omega))
    set xb' := ψ (c.Dv γ f) with hxb'
    have hxb_RF : xb' ∈ c''.RF J'.e b := by
      have hm1 := Chart.Dv_mem_RF_of_lowersBy c'' c' J'.e _ hlow (pushIdx hnn γ)
        (by rw [hRF]; exact hψf J' hJ' : ψ f ∈ c''.RF J'.e 1)
      rw [hT.compat.Dv, lam_compl_pad hsupp, hlamγ] at hm1
      have htq : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j β := by exact_mod_cast htailγ
      have hm2 : 1 - (lam e β + b * (tailSum j γ : ℚ)) = b := by
        have := hkey; rw [← htq] at this; linarith
      rw [hm2] at hm1
      exact hm1
    have hxb_mem : xb' ∈ maximalIdeal R' := hc''.RF_le_maximalIdeal hbpos hxb_RF
    have hdl : c'.d (Fin.castLE hnn l) xb' = ψ u := by rw [hxb', hT.compat.d, hu]
    have hdl_nm : c'.d (Fin.castLE hnn l) xb' ∉ maximalIdeal R' := by
      rw [hdl]; exact notMem_maximalIdeal.2 ((Units.isUnit u).map ψ)
    obtain ⟨m, hm, hmnm⟩ : ∃ m : Fin n', j ≤ (m : ℕ) ∧ c''.d m xb' ∉ maximalIdeal R' := by
      by_contra hcon
      push Not at hcon
      apply hdl_nm
      rw [c''.eq_sum (c'.d (Fin.castLE hnn l)), Derivation.sum_apply']
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [Derivation.smul_apply, smul_eq_mul]
      by_cases hmj : (m : ℕ) < j
      · rw [hx m hmj, c'.d_x, ite_eq_right (fun h => by rw [← h] at hmj; simp at hmj; omega), zero_mul]
        exact zero_mem _
      · exact Ideal.mul_mem_left _ _ (hcon m (by omega))
    have hJ'm : J'.e m = b := by
      refine le_antisymm ?_ ?_
      · rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by omega))
      · by_contra hlt'
        push Not at hlt'
        have := (hc''.mem_RF_iff J'.nonneg b xb').1 hxb_RF (Finsupp.single m 1) (by
          rw [lam_single]; simpa using hlt')
        rw [Chart.coeff_tau_eq_zero_iff, Chart.Dv_single_one] at this
        exact hmnm this
    obtain ⟨u', hu'⟩ := notMem_maximalIdeal.1 hmnm
    refine ⟨(c''.replace m xb' u' hu'.symm).reindex (Equiv.swap jj' m),
      (hc''.replace m xb' u' hu'.symm hxb_mem).reindex _, fun t => ?_, fun i hi => ?_⟩
    · rw [Chart.RF_reindex _ _ (fun i => by
          rcases eq_or_ne i jj' with h | h
          · rw [h, Equiv.swap_apply_left, hJ'm, hJ'j]
          · rcases eq_or_ne i m with h' | h'
            · rw [h', Equiv.swap_apply_right, hJ'm, hJ'j]
            · rw [Equiv.swap_apply_of_ne_of_ne h h'])]
      rw [hc''.RF_replace J'.nonneg m xb' u' hu'.symm hxb_mem (by rw [hJ'm]; exact hxb_RF), hRF]
    · show ((c''.replace m xb' u' hu'.symm).reindex (Equiv.swap jj' m)).x i =
        (nextChart c' jj' (Fin.castLE hnn l) xb' (Units.map ψ.toMonoidHom u) _).x i
      simp only [Principalization.nextChart, Chart.reindex_x]
      by_cases hij : (i : ℕ) < j
      · have h1 : i ≠ jj' := fun h => by rw [h] at hij; omega
        have h2 : i ≠ m := fun h => by rw [h] at hij; omega
        have h3 : i ≠ Fin.castLE hnn l := fun h => by rw [h] at hij; simp at hij; omega
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h3,
          c''.replace_x_ne _ _ _ _ h2, c'.replace_x_ne _ _ _ _ h3, hx i hij]
      · have hieq : i = jj' := Fin.ext (by omega)
        subst hieq
        rw [Equiv.swap_apply_left, Equiv.swap_apply_left, c''.replace_x_self, c'.replace_x_self]

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] {R' : Type*} [CommRing R'] [Algebra ℚ R']
  [IsLocalRing R'] [IsNoetherianRing R'] {n n' : ℕ} {hnn : n ≤ n'}

lemma nextE_zero_ge {e : Fin n → ℚ} {j : ℕ} (b : ℚ) (i : Fin n) (hi : j + 1 ≤ (i : ℕ)) :
    nextE e j b i = 0 := by
  simp only [nextE, ite_eq_right (show ¬ (i : ℕ) < j by omega), ite_eq_right (show ¬ (i : ℕ) = j by omega)]

/-- Runs keep the weights supported below the stage. -/
lemma IsRun.supp {I : Ideal S} {j : ℕ} {c : Chart S n} {e : Fin n → ℚ} {k : ℕ} {ck : Chart S n}
    {ek : Fin n → ℚ} (h : IsRun I j c e k ck ek) (hsupp : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0) :
    ∀ i : Fin n, k ≤ (i : ℕ) → ek i = 0 := by
  induction h with
  | refl => exact hsupp
  | step hj f hf β l hl hβl hlam hN hunit hb u hu hnext ih =>
    exact ih fun i hi => nextE_zero_ge _ i hi

/-- **Transfer theorem** (inductive form). -/
theorem IsRun.transfer {ψ : S →+* R'} {I : Ideal S} {j : ℕ} {c : Chart S n} {e : Fin n → ℚ}
    {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ} (h : IsRun I j c e k ck ek)
    (hsupp : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0) :
    ∀ c' : Chart R' n', TI hnn ψ I j c e c' → ∃ ck' : Chart R' n', TI hnn ψ I k ck ek ck' := by
  induction h with
  | refl => exact fun c' hT => ⟨c', hT⟩
  | step hj f hf β l hl hβl hlam hN hunit hb u hu hnext ih =>
    intro c' hT
    exact ih (fun i hi => nextE_zero_ge _ i hi) _
      (hT.step hj hsupp f hf β l hl hβl hlam hN hunit u hu)

omit [IsNoetherianRing R'] in
/-- The transfer invariant holds at stage `0` for compatible charts. -/
lemma TI.zero {ψ : S →+* R'} {I : Ideal S} {c : Chart S n} {c' : Chart R' n'}
    (h : Compat hnn ψ c c') : TI hnn ψ I 0 c 0 c' :=
  ⟨h, fun _ _ _i hi => absurd hi (Nat.not_lt_zero _),
    fun J' _ _ => ⟨J'.c, J'.centred, fun _ => rfl, fun _i hi => absurd hi (Nat.not_lt_zero _)⟩⟩

/-- **Transfer theorem.** A Method-1 run for `I` on `S`, transported along `ψ : S → R'` with a
compatible chart, bounds the admissible marked centres of `I R'` from below (lexicographically in
the weights, i.e. from above in the invariant), and identifies those with equal weights. -/
theorem IsRun.transfer_bound {ψ : S →+* R'} {I : Ideal S} {c : Chart S n} {k : ℕ}
    {ck : Chart S n} {ek : Fin n → ℚ} (h : IsRun I 0 c 0 k ck ek) {c' : Chart R' n'}
    (hc : Compat hnn ψ c c') :
    ∃ ck' : Chart R' n', Compat hnn ψ ck ck' ∧ ∀ J' : MC R' n', J'.Adm (I.map ψ) →
      toLex (pad n' ek) ≤ toLex J'.e ∧
      (J'.e = pad n' ek → ∀ t, J'.RF t = ck'.RF (pad n' ek) t) := by
  obtain ⟨ck', hT⟩ := h.transfer (fun _ _ => rfl) c' (TI.zero hc)
  have hsk := h.supp (fun _ _ => rfl)
  refine ⟨ck', hT.compat, fun J' hJ' => ⟨?_, fun he t => ?_⟩⟩
  · rw [← not_lt]
    rintro ⟨i, hbelow, hlt⟩
    simp only [Pi.toLex_apply] at hbelow hlt
    by_cases hik : (i : ℕ) < k
    · exact absurd (hT.max J' hJ' i hik fun i' hi' => hbelow i' hi') (not_le.2 hlt)
    · rw [pad_zero_ge hsk i (by omega)] at hlt
      exact absurd (J'.nonneg i) (not_le.2 hlt)
  · obtain ⟨c'', -, hRF, hx⟩ := hT.dom J' hJ' (fun i _ => by rw [he])
    rw [← hRF, he]
    refine Chart.RF_congr (fun i hi => hx i ?_) t
    by_contra hik
    exact hi (pad_zero_ge hsk i (by omega))

end BezoutCounterexample.Principalization
