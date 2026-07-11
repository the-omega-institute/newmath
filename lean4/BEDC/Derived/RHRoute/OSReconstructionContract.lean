import BEDC.Derived.RHRoute.OCLSDTickReflection

/-
Carrier-relative Osterwalder–Schrader reconstruction contract for the OCLSD tick
(innovation-geometry 定理 8.4, `H = -ΔT⁻¹ log P`).

`OCLSDTickReflection` discharges, in finite located-rational data, exactly the *hypothesis* of
the OS reconstruction theorem: a tick is reflection-positive (`TickReflectionPositive`) iff its
2-state transition operator is PSD, and a single rational check on the antisymmetric mode
decides it (`reflectionPositive_of_flip_nonneg`).  The reconstruction theorem itself then says:
from a reflection-positive transition operator `P` one builds the physical Hilbert space, the
positive self-adjoint generator `H = -ΔT⁻¹ log P`, and the unitary flow `e^{itH}`.

That construction is analytic — located operator logarithm, monotone spectral calculus, a GNS
passage — none of which this mathlib-free located-rational layer builds.  So the honest encoding
is a **carrier contract**, the same Setup-typeclass discipline as `DiagonalHilbertKit`:

* `OSReconstructionKit` *posits* the analytic carrier (time axis, transfer / generator /
  unitary operator types, the self-adjoint / nonnegative / unitary predicates, the `logGen`
  and heat-semigroup operations).  It is an OBLIGATION, not a construction.
* `OSReconstruction` is the reconstruction *output* for one tick: a generator with its
  self-adjointness / nonnegativity / unitary-flow certificates and the heat-kernel identity
  `e^{-ΔT·H} = P_g` recovering the tick's transfer operator.
* `OSReconstructionCarrier` bundles the obligation as a field `reconstruct` consuming a
  reflection-positive tick.

The bridge theorems are then honest: *given* a carrier (i.e. given the analytic obligation
discharged), the finite reflection-positivity classification feeds the reconstruction.  We
deliberately do NOT prove `ReflectionPositiveInput → Nonempty OSReconstructionCarrier`: that is
inhabitable by an all-`Unit` carrier and would be a fake witness for the analytic wall.  No
concrete `OSReconstructionCarrier` instance is supplied here; the located operator logarithm /
spectral calculus, together with `SpectralZeroIdentity`, remain the walls.  0-axiom /
propext-free.
-/

namespace BEDC.Derived.RHRoute.OSReconstructionContract

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.OCLSDReflectionForm
open BEDC.Derived.RHRoute.OCLSDTickReflection
open BEDC.Derived.RHRoute.LocatedGenerationTower

universe u
variable {K : DynamicsTypes}

/-- The **posited analytic carrier** for OS reconstruction (定理 8.4).  Every field names a
piece of the reconstruction obligation; no field is constructed in this layer.

* `Time` — the located time axis (the flow parameter `t`);
* `TransferOp` / `Hamiltonian` / `UnitaryOp` — transition operators `P`, generators `H`,
  unitaries `U`;
* `SelfAdjoint` / `Nonnegative` / `Unitary` — the operator predicates;
* `transferOfTick g` — the tick's 2-state transition operator `P_g`;
* `deltaT` — the tick duration `ΔT`;
* `logGen P` — the analytic core `H = -ΔT⁻¹ log P` (located operator logarithm);
* `heatSemigroup H t` — `e^{-tH}` (states the recovery `e^{-ΔT·H}=P`);
* `flow H t` — the unitary group `e^{itH}`. -/
structure OSReconstructionKit (K : DynamicsTypes) where
  Time : Type u
  TransferOp : Type u
  Hamiltonian : Type u
  UnitaryOp : Type u
  SelfAdjoint : Hamiltonian → Prop
  Nonnegative : Hamiltonian → Prop
  Unitary : UnitaryOp → Prop
  transferOfTick : RawGenerationStep K → TransferOp
  deltaT : Time
  logGen : TransferOp → Hamiltonian
  heatSemigroup : Hamiltonian → Time → TransferOp
  flow : Hamiltonian → Time → UnitaryOp

/-- The **reconstruction output** for one reflection-positive tick `g`: the generator `H` with
its self-adjointness, nonnegativity and unitary-flow certificates, plus the heat-kernel identity
`e^{-ΔT·H} = P_g` that pins `H` as the true reconstruction of the tick's transition operator. -/
structure OSReconstruction (kit : OSReconstructionKit K)
    (g : RawGenerationStep K) where
  gen : kit.Hamiltonian
  gen_isLog : gen = kit.logGen (kit.transferOfTick g)
  gen_selfAdjoint : kit.SelfAdjoint gen
  gen_nonneg : kit.Nonnegative gen
  flow_unitary : (t : kit.Time) → kit.Unitary (kit.flow gen t)
  heat_recovers : kit.heatSemigroup gen kit.deltaT = kit.transferOfTick g

/-- An **OS reconstruction carrier** for a tick-reflection kit `rk`: the analytic obligation,
packaged as a function that turns a reflection-positive tick into its reconstruction.  Supplying
an instance means discharging 定理 8.4's analytic content; none is supplied here. -/
structure OSReconstructionCarrier (rk : TickReflectionKit K) where
  kit : OSReconstructionKit K
  reconstruct : (g : RawGenerationStep K) → TickReflectionPositive rk g →
    OSReconstruction kit g

/-- **定理 8.4, carrier-relative.**  Given the reconstruction obligation packaged as a carrier
`C`, every reflection-positive tick has an OS reconstruction.  Honest content: the reflection-
positivity hypothesis (finite, discharged in `OCLSDTickReflection`) is exactly what the carrier
consumes; the analytic construction lives in `C.reconstruct`. -/
def theorem_8_4_carrier_relative {rk : TickReflectionKit K}
    (C : OSReconstructionCarrier rk) (g : RawGenerationStep K)
    (hRP : TickReflectionPositive rk g) :
    OSReconstruction C.kit g :=
  C.reconstruct g hRP

/-- **The finite rational check feeds the reconstruction.**  A tick whose OS reflection form is
`≥ 0` on the antisymmetric mode `(1,-1)` — a single located-rational inequality — is
reflection-positive (`reflectionPositive_of_flip_nonneg`), hence, against any carrier, admits an
OS reconstruction.  This is the exact junction between the proven finite classification and the
posited analytic obligation. -/
def theorem_8_4_from_finite_RP {rk : TickReflectionKit K}
    (C : OSReconstructionCarrier rk) (g : RawGenerationStep K)
    (hflip : ratLe ratZero (tickReflectionForm rk g ratOne (ratNeg ratOne))) :
    OSReconstruction C.kit g :=
  C.reconstruct g (reflectionPositive_of_flip_nonneg rk g hflip)

/-- On a reflection-positive input every tick reconstructs (whole-input form of 定理 8.4,
carrier-relative). -/
def input_reconstructs {rk : TickReflectionKit K}
    (C : OSReconstructionCarrier rk) (hRP : ReflectionPositiveInput rk)
    (g : RawGenerationStep K) :
    OSReconstruction C.kit g :=
  C.reconstruct g (hRP g)

end BEDC.Derived.RHRoute.OSReconstructionContract
