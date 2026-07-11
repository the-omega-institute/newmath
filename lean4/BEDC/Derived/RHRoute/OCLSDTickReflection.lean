import BEDC.Derived.RHRoute.OCLSDReflectionForm
import BEDC.Derived.RHRoute.OCLSDHamiltonian

/-
Wiring the finite reflection-positivity ⟺ PSD classification (OCLSDReflectionForm) into the
OCLSD tick dynamics.

`OCLSDReflectionForm` proved the standalone 2-state result (osForm, reflection_holds /
reflection_fails).  This module parameterises it by the actual OCLSD tick: each
`RawGenerationStep` carries a located transition weight `q`, its OS reflection form is
`osForm q`, and a tick is *reflection-positive* iff `2q ≤ 1` (its transition operator is PSD).
Lifting `reflection_holds` / `reflection_fails` gives the per-tick and whole-input
classification — exactly the class of OCLSD tick inputs admitting a unitary OS reconstruction
(the positivity condition behind `OCLSDHamiltonian`'s posited self-adjoint `H_OCLSD` / unitary
phase flow; innovation-geometry 定理 8.3 / 命题 8.5).

Honest boundary: this classifies the tick inputs by a *finite rational* reflection-positivity
condition.  It does NOT discharge the OS-reconstruction analytic content (定理 8.4, `H = -ln
P/ΔT`), and it does NOT touch `SpectralZeroIdentity` (the Hilbert–Pólya wall).  0-axiom /
propext-free.
-/

namespace BEDC.Derived.RHRoute.OCLSDTickReflection

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.OCLSDReflectionForm
open BEDC.Derived.RHRoute.LocatedGenerationTower

universe u
variable {K : DynamicsTypes}

/-- Reflection-form data on the OCLSD tick: each raw tick carries a located transition weight
`tickQ g` (its "flip weight", `0 ≤ q`).  The tick's OS reflection form is `osForm (tickQ g)`. -/
structure TickReflectionKit (K : DynamicsTypes) where
  tickQ : RawGenerationStep K → RatNum
  tickQ_nonneg : (g : RawGenerationStep K) → ratLe ratZero (tickQ g)

/-- The per-tick OS reflection quadratic form `⟨θf, f⟩` for the tick `g`. -/
def tickReflectionForm (kit : TickReflectionKit K) (g : RawGenerationStep K)
    (f0 f1 : RatNum) : RatNum :=
  osForm (kit.tickQ g) f0 f1

/-- A tick is **reflection-positive** iff `2q ≤ 1` — its 2-state transition operator is PSD. -/
def TickReflectionPositive (kit : TickReflectionKit K) (g : RawGenerationStep K) : Prop :=
  ratLe (ratMul twoRat (kit.tickQ g)) ratOne

/-- **Reflection-positive tick ⟹ its OS form is `≥ 0` on every mode** (定理 8.3, lifted to the
OCLSD tick): the tick admits a unitary OS reconstruction. -/
theorem tick_reflection_holds (kit : TickReflectionKit K) (g : RawGenerationStep K)
    (h : TickReflectionPositive kit g) (f0 f1 : RatNum) :
    ratLe ratZero (tickReflectionForm kit g f0 f1) :=
  reflection_holds (kit.tickQ g) f0 f1 (kit.tickQ_nonneg g) h

/-- **Reflection-anticorrelated tick (`2q > 1`) ⟹ its OS form is `< 0` on the antisymmetric
mode** (命题 8.5, lifted): an explicit indefinite tick with NO unitary reconstruction — the
reflection-positivity signature is a classification condition on the OCLSD tick, not a
postulate. -/
theorem tick_reflection_fails (kit : TickReflectionKit K) (g : RawGenerationStep K)
    (h : ratLt ratOne (ratMul twoRat (kit.tickQ g))) :
    ratLt (tickReflectionForm kit g ratOne (ratNeg ratOne)) ratZero :=
  reflection_fails (kit.tickQ g) h

/-- A **reflection-positive tick input**: every raw tick is reflection-positive.  This is
exactly the class of OCLSD inputs with a unitary OS reconstruction. -/
def ReflectionPositiveInput (kit : TickReflectionKit K) : Prop :=
  ∀ g : RawGenerationStep K, TickReflectionPositive kit g

/-- On a reflection-positive input, every tick's OS form is `≥ 0` on every mode (full
reflection positivity of the whole tick input). -/
theorem input_reflection_holds (kit : TickReflectionKit K)
    (hRP : ReflectionPositiveInput kit) (g : RawGenerationStep K) (f0 f1 : RatNum) :
    ratLe ratZero (tickReflectionForm kit g f0 f1) :=
  tick_reflection_holds kit g (hRP g) f0 f1

/-- **Converse (the antisymmetric mode is the sharp test): if the tick's OS form is `≥ 0` on
the antisymmetric mode `(1,-1)`, the tick IS reflection-positive.**  Together with
`tick_reflection_holds` this gives the full characterisation `TickReflectionPositive g ⟺
(OS form ≥ 0 on (1,-1))` — a single computable rational check on the tick decides its
reconstructability. -/
theorem reflectionPositive_of_flip_nonneg (kit : TickReflectionKit K) (g : RawGenerationStep K)
    (h : ratLe ratZero (tickReflectionForm kit g ratOne (ratNeg ratOne))) :
    TickReflectionPositive kit g := by
  have h' : ratLe ratZero (ratMul (oneMinusTwoQ (kit.tickQ g)) twoRat) :=
    ratLe_of_RatEq_right h (osForm_one_negOne_eq (kit.tickQ g))
  have hsub : ratLe ratZero (oneMinusTwoQ (kit.tickQ g)) :=
    ratMul_le_cancel_right ratZero_lt_twoRat
      (ratLe_of_RatEq_left (ratMul_zero_left twoRat) h')
  exact ratLe_of_sub_nonneg (ratMul twoRat (kit.tickQ g)) ratOne hsub

/-- Non-vacuity: the trivial kit `q ≡ 0` is a reflection-positive input (every tick has
`2·0 = 0 ≤ 1`).  So the reflection-positive class is inhabited over any dynamics-type. -/
def trivialKit (K : DynamicsTypes) : TickReflectionKit K where
  tickQ := fun _ => ratZero
  tickQ_nonneg := fun _ => ratLe_refl ratZero

theorem trivialKit_reflectionPositive (K : DynamicsTypes) :
    ReflectionPositiveInput (trivialKit K) := by
  intro _g
  show ratLe (ratMul twoRat ratZero) ratOne
  exact ratLe_of_RatEq_left (RatEq_symm (ratMul_zero_right twoRat)) ratZero_le_one

end BEDC.Derived.RHRoute.OCLSDTickReflection
