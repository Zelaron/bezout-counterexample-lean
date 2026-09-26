import Mathlib

/-!
# A countable Bézout domain without the elementary divisor property: definitions

This file contains the basic definitions used in the formalization of

  C. Hägg, A. Mörtberg, *A countable Bézout domain without the elementary divisor property*
  (`bezout-counterexample.tex`).

* `IsSmithNormalForm`, `MatrixEquivalent`, `HasSmithNormalForm`, `IsElementaryDivisorDomain`
  (Section 1 of the paper);
* `RealPt A`: the real points `Spec(A)(ℝ)` of a ring `A`, i.e. ring homomorphisms `A → ℝ`,
  with the weak topology (for finitely generated `ℚ`-algebras this is the Euclidean topology);
* `IsMonotoneSurjection`: continuous surjections with connected fibres (Section 2);
* `Mreal a b` and `LineFieldOrientable`: the real line field `z ↦ im M(z)` and its orientability
  (existence of a continuous nowhere vanishing section), Section 2;
* `SmoothFactorialDomain`: smooth finitely generated factorial `ℚ`-domains;
* `PrincipalizationExtension`: the statement of Proposition 4.6 (`prop:principalization-extension`)
  of the paper, proved as `Principalization.principalizationExtension`.
* The initial data `A₀ = ℚ[x,y]`, `Δ = x² + y² - 1`, `M = [[1+x, y], [y, 1-x]]` (1.1).
-/

noncomputable section

namespace BezoutCounterexample

open MvPolynomial

/-! ## Smith normal form and elementary divisor domains -/

section SNF

variable {R : Type*} [CommRing R]

/-- A matrix `D` is in *Smith normal form* if it is diagonal with diagonal entries
`d 0, d 1, …` satisfying `d k ∣ d (k+1)`. Since `0 ∣ a` forces `a = 0`, this is equivalent to the
formulation of the paper: the nonzero diagonal entries occur first and satisfy
`d₁ ∣ d₂ ∣ ⋯ ∣ d_r` (see `isSmithNormalForm_iff`). -/
def IsSmithNormalForm {m n : ℕ} (D : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ d : ℕ → R, (∀ i j, D i j = if (i : ℕ) = (j : ℕ) then d i else 0) ∧
    ∀ k, k + 1 < min m n → d k ∣ d (k + 1)

/-- Two `m × n` matrices `F` and `G` are *equivalent* if `P F Q = G` for some
`P ∈ GL_m(R)` and `Q ∈ GL_n(R)`. -/
def MatrixEquivalent {m n : ℕ} (F G : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ (P : GL (Fin m) R) (Q : GL (Fin n) R),
    (P : Matrix (Fin m) (Fin m) R) * F * (Q : Matrix (Fin n) (Fin n) R) = G

/-- `F` has a Smith normal form if it is equivalent to a matrix in Smith normal form. -/
def HasSmithNormalForm {m n : ℕ} (F : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ G, MatrixEquivalent F G ∧ IsSmithNormalForm G

variable (R) in
/-- A domain is an *elementary divisor domain* if every finite matrix over it has a Smith
normal form. -/
def IsElementaryDivisorDomain : Prop :=
  IsDomain R ∧ ∀ (m n : ℕ) (F : Matrix (Fin m) (Fin n) R), HasSmithNormalForm F

end SNF

/-! ## Real points -/

/-- The real points `Spec(A)(ℝ)` of a commutative ring `A`: ring homomorphisms `A → ℝ`.
(For a `ℚ`-algebra these are automatically `ℚ`-algebra homomorphisms.) -/
def RealPt (A : Type*) [CommRing A] : Type _ := A →+* ℝ

namespace RealPt

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

instance : FunLike (RealPt A) A ℝ := inferInstanceAs (FunLike (A →+* ℝ) A ℝ)

instance : RingHomClass (RealPt A) A ℝ := inferInstanceAs (RingHomClass (A →+* ℝ) A ℝ)

/-- View a ring homomorphism `A → ℝ` as a real point. -/
def ofHom (φ : A →+* ℝ) : RealPt A := φ

/-- The ring homomorphism underlying a real point. -/
def toHom (z : RealPt A) : A →+* ℝ := z

@[simp] lemma ofHom_apply (φ : A →+* ℝ) (a : A) : ofHom φ a = φ a := rfl

@[simp] lemma toHom_apply (z : RealPt A) (a : A) : toHom z a = z a := rfl

@[ext] lemma ext {z w : RealPt A} (h : ∀ a, z a = w a) : z = w := DFunLike.ext _ _ h

/-- The *weak topology* on real points: the coarsest topology for which every evaluation
`z ↦ z a` is continuous. For a finitely generated `ℚ`-algebra this is the Euclidean topology. -/
instance : TopologicalSpace (RealPt A) :=
  TopologicalSpace.induced (fun z : RealPt A => (z : A → ℝ)) inferInstance

lemma continuous_eval (a : A) : Continuous fun z : RealPt A => z a :=
  (continuous_apply a).comp continuous_induced_dom

lemma continuous_iff {X : Type*} [TopologicalSpace X] {g : X → RealPt A} :
    Continuous g ↔ ∀ a, Continuous fun t => g t a := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

instance : T2Space (RealPt A) :=
  (Topology.IsEmbedding.mk ⟨rfl⟩ (fun _ _ h => DFunLike.coe_injective h) :
    Topology.IsEmbedding fun z : RealPt A => (z : A → ℝ)).t2Space

/-- Pullback of real points along a ring homomorphism, `Spec(B)(ℝ) → Spec(A)(ℝ)`. -/
def comap (f : A →+* B) (z : RealPt B) : RealPt A := (toHom z).comp f

@[simp] lemma comap_apply (f : A →+* B) (z : RealPt B) (a : A) : comap f z a = z (f a) := rfl

lemma continuous_comap (f : A →+* B) : Continuous (comap f) :=
  continuous_iff.2 fun a => continuous_eval (f a)

lemma comap_comp (f : A →+* B) (g : B →+* C) (z : RealPt C) :
    comap (g.comp f) z = comap f (comap g z) := rfl

end RealPt

/-! ## Monotone surjections -/

/-- A *monotone surjection*: a continuous surjection all of whose fibres are connected.
(In the paper the spaces are moreover compact Hausdorff; these hypotheses are imposed
separately where they are needed.) -/
structure IsMonotoneSurjection {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) : Prop where
  continuous : Continuous q
  surjective : Function.Surjective q
  isConnected_fiber : ∀ y, IsConnected (q ⁻¹' {y})

/-- `q` restricts to a monotone surjection `K' → K`. -/
def IsMonotoneSurjOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (K' : Set X) (K : Set Y) : Prop :=
  ∃ h : Set.MapsTo q K' K, IsMonotoneSurjection (h.restrict q K' K)

/-! ## The line field `im M` and orientability -/

/-- The real matrix `M(a,b) = [[1+a, b], [b, 1-a]]`. -/
def Mreal (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + a, b; b, 1 - a]

/-- Given functions `X Y : K → ℝ` (in practice with `X² + Y² = 1`, so that `M(X z, Y z)` has
rank one), the real line bundle `z ↦ im M(X z, Y z)` is *orientable* if it admits a continuous
nowhere vanishing section. (On compact Hausdorff spaces this is equivalent to the existence of an
orientation, as recalled in Section 2 of the paper.) -/
def LineFieldOrientable {K : Type*} [TopologicalSpace K] (X Y : K → ℝ) : Prop :=
  ∃ v : K → Fin 2 → ℝ, Continuous v ∧
    ∀ z, v z ≠ 0 ∧ v z ∈ Set.range (Mreal (X z) (Y z)).mulVec

/-! ## The initial data (1.1) -/

/-- `A₀ = ℚ[x,y]`. -/
abbrev A₀ : Type := MvPolynomial (Fin 2) ℚ

/-- The variable `x`. -/
def x : A₀ := X 0

/-- The variable `y`. -/
def y : A₀ := X 1

/-- `Δ = x² + y² - 1`. -/
def Δ : A₀ := x ^ 2 + y ^ 2 - 1

/-- `M = [[1+x, y], [y, 1-x]]`. -/
def M : Matrix (Fin 2) (Fin 2) A₀ := !![1 + x, y; y, 1 - x]

/-- The circle `K₀ = {(x,y) ∈ ℝ² : x² + y² = 1}`, as a set of real points of `A₀`. -/
def K₀ : Set (RealPt A₀) := {z | z Δ = 0}

/-! ## Smooth finitely generated factorial `ℚ`-domains and Proposition 4.6 -/

/-- A smooth finitely generated factorial `ℚ`-domain (`Algebra.Smooth` includes finite
presentation). -/
structure SmoothFactorialDomain where
  /-- The underlying ring. -/
  carrier : Type
  [commRing : CommRing carrier]
  [isDomain : IsDomain carrier]
  [algebra : Algebra ℚ carrier]
  [smooth : Algebra.Smooth ℚ carrier]
  [ufd : UniqueFactorizationMonoid carrier]

attribute [instance] SmoothFactorialDomain.commRing SmoothFactorialDomain.isDomain
  SmoothFactorialDomain.algebra SmoothFactorialDomain.smooth SmoothFactorialDomain.ufd

instance : CoeSort SmoothFactorialDomain Type := ⟨SmoothFactorialDomain.carrier⟩

/-- **Proposition 4.6** (`prop:principalization-extension`) of the paper, as a statement:

Let `A` be a smooth finitely generated factorial `ℚ`-domain, let `I ⊂ A` be a nonzero finitely
generated ideal, and let `K ⊂ Spec(A)(ℝ)` be compact. There are a smooth finitely generated
factorial `ℚ`-domain `A'`, an injection `A ↪ A'`, and a compact set `K' ⊂ Spec(A')(ℝ)` such that
`IA'` is principal and the induced map `K' → K` is a monotone surjection.

It is proved as `Principalization.principalizationExtension` (`Principalization/RealPts.lean`),
by weighted principalization carried out on Jouanolou torsors over extended Rees algebras. -/
def PrincipalizationExtension : Prop :=
  ∀ (A : SmoothFactorialDomain) (I : Ideal A) (K : Set (RealPt A)),
    I ≠ ⊥ → I.FG → IsCompact K →
    ∃ (A' : SmoothFactorialDomain) (f : A →ₐ[ℚ] A') (K' : Set (RealPt A')),
      Function.Injective f ∧ (I.map f).IsPrincipal ∧ IsCompact K' ∧
        IsMonotoneSurjOn (RealPt.comap (f : A →+* A')) K' K

end BezoutCounterexample
