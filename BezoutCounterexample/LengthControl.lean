import BezoutCounterexample.Torsor

/-!
# Section 4.3: bounding the length of the invariant (Lemma 4.4)

Termination requires a bound on the number of nonzero entries of the invariants; this is not
automatic, because the dimension of the rings grows.

Fix `N ≥ 0`. For a smooth finitely generated `ℚ`-domain `B`, a nonzero ideal `𝔟 ⊆ B`, and an integer
`m ≥ 0`, the condition `(⋆_N)` on `(B, 𝔟, m)` (`Star N 𝔟 m`) is:
1. `dim B ≤ N + m`;
2. for every maximal ideal `𝔪 ⊇ 𝔟` there are `ℚ`-derivations `δ₁, …, δ_m` of `B` and elements
   `z₁, …, z_m ∈ B` with `δⱼ(𝔟) ⊆ 𝔟` for every `j` and `det(δⱼ(z_q)) ∉ 𝔪` (the determinant of the
   empty matrix is `1`).

By Lemma 3.7(2), if `(B, 𝔟, m)` satisfies `(⋆_N)`, then every invariant of `𝔟` has at most `N`
nonzero entries (`Star.numNonzero_inv_le`). The triple `(A, I, 0)` satisfies `(⋆_{dim A})`
(`star_initial`).

**Lemma 4.4** (`lem:length-control`): `length_control_divisorial`, `length_control_torsor`.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization

/-- The condition `(⋆_N)` on `(B, 𝔟, m)`. -/
structure Star (N : ℕ) {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]
    (𝔟 : Ideal B) (m : ℕ) : Prop where
  dim_le : ringKrullDim B ≤ ((N + m : ℕ) : WithBot ℕ∞)
  derivations : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → 𝔟 ≤ 𝔪 →
    ∃ (δ : Fin m → Derivation ℚ B B) (z : Fin m → B), (∀ j, ∀ f ∈ 𝔟, δ j f ∈ 𝔟) ∧
      (Matrix.of fun j q => δ j (z q)).det ∉ 𝔪

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]

/-- By Lemma 3.7(2), under `(⋆_N)` every invariant of `𝔟` has at most `N` nonzero entries. -/
theorem Star.numNonzero_inv_le {N m : ℕ} {𝔟 : Ideal B} (h : Star N 𝔟 m) (h𝔟 : 𝔟 ≠ ⊥)
    (𝔪 : Ideal B) [𝔪.IsMaximal] (h𝔟𝔪 : 𝔟 ≤ 𝔪) : numNonzero (inv 𝔟 𝔪) ≤ N := by
  obtain ⟨δ, z, hδ, hdet⟩ := h.derivations 𝔪 inferInstance h𝔟𝔪
  have h1 := (numNonzero_inv_add_le h𝔟 h𝔟𝔪 δ hδ z hdet).trans h.dim_le
  have h2 : numNonzero (inv 𝔟 𝔪) + m ≤ N + m := by exact_mod_cast h1
  omega

/-- The triple `(A, I, 0)` satisfies `(⋆_{dim A})`. -/
theorem star_initial {N : ℕ} (hN : ringKrullDim B = N) (𝔟 : Ideal B) : Star N 𝔟 0 := by
  refine ⟨by rw [hN]; simp, fun 𝔪 h𝔪 _ => ⟨Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, ?_⟩⟩
  rw [Matrix.det_isEmpty]
  exact (Ideal.ne_top_iff_one _).1 h𝔪.ne_top

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [UniqueFactorizationMonoid A]

namespace PrincipalizationData

variable (S : PrincipalizationData A)

/-- **Lemma 4.4** (`lem:length-control`), divisorial step: if `(A, I, m)` satisfies `(⋆_N)`, then
so does `(A, I₁, m)`, `I₁ = (I : π^a)`. -/
theorem length_control_divisorial {N m : ℕ} (hS : Star N S.I m) (hk : S.k = 1) {a : ℕ}
    (ha : S.e 0 = 1 / (a : ℚ)) : Star N (S.divI₁ a) m :=
  ⟨hS.dim_le, div_vertOK S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw (S.divisorial_𝔭_eq hk)
    (S.a_pos hk ha) hS.derivations⟩

/-- In the torsor step, `dim U = dim A + 1 + ℓ`. -/
theorem ringKrullDim_U : ringKrullDim S.U = ringKrullDim A + ((1 + S.ℓ : ℕ) : WithBot ℕ∞) := by
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal S.U
  obtain ⟨nA, ⟨cA⟩⟩ := exists_chart_atPrime (Q.comap (algebraMap A S.U))
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem S.ne_bot S.hmax S.h𝔭 S.π_mem_fil Q
  obtain ⟨nP, ⟨cP⟩⟩ := exists_chart_atPrime (Q.comap (algebraMap S.𝓡 S.U))
  have hnP : nP = nA + 1 :=
    rees_chart_card _ (fun j hj => compFil_F_nonpos S.ne_bot S.hmax S.h𝔭 S.d hj) _ cA _ cP
  obtain ⟨cU⟩ := chart_of_mvLoc (S := Localization.AtPrime (Q.comap (algebraMap S.𝓡 S.U)))
    (S' := Localization.AtPrime Q) (theta2 S.h Q hl) (theta2_injective _ Q hl)
    (theta2_surj _ Q hl) cP
  rw [chart_size_eq_ringKrullDim cU, chart_size_eq_ringKrullDim cA, hnP]
  norm_cast
  omega

/-- **Lemma 4.4** (`lem:length-control`), torsor step: if `(A, I, m)` satisfies `(⋆_N)`, then
`(U, I₁, m + ℓ + 1)` satisfies `(⋆_N)`. -/
theorem length_control_torsor {N m : ℕ} (hS : Star N S.I m) (_hk : 2 ≤ S.k) :
    Star N S.I₁ (m + S.ℓ + 1) := by
  refine ⟨?_, ?_⟩
  · -- `dim U = dim A + 1 + ℓ ≤ N + m + 1 + ℓ`
    rw [S.ringKrullDim_U]
    have h := hS.dim_le
    obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast A
    rw [hn] at h ⊢
    have h' : n ≤ N + m := by exact_mod_cast h
    norm_cast
    omega
  · -- the lifted, Euler and vertical derivations (engine: `torsor_vertOK`)
    have := torsor_vertOK S.ne_bot S.hmax S.h𝔭 S.d_pos S.hw S.π_mem_fil hS.derivations
    exact this

end PrincipalizationData

end BezoutCounterexample
