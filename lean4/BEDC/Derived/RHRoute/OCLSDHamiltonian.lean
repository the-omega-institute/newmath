import BEDC.Derived.RHRoute.OCLSDSpectral

/-
The self-adjoint OCLSD Hamiltonian (Hilbert–Pólya operator side, ζ-free).

Completes the operator half of the OCLSD Hilbert–Pólya reformulation from
`OCLSDSpectral`: the diagonal operator $H_{\mathrm{OCLSD}}$ whose orthonormal basis
is the forward orbits and whose eigenvalue on an orbit is that orbit's cumulative
angular height. Because those heights are located-REAL, $H_{\mathrm{OCLSD}}$ is
self-adjoint, and its phase flow $U(\tau)=e^{i\tau H_{\mathrm{OCLSD}}}$ is unitary.

Everything here is ζ-free: the diagonal-on-ONB Hilbert kit is an abstract interface
(carrier implements self-adjointness / unitarity — Setup path, no mathlib Hilbert
theory), and the OCLSD Hamiltonian is just `diag` of the orbit-height eigenfunction.
The only remaining wall is the spectrum-to-zeros identity `SpectralZeroIdentity`
(that the real spectrum of $H_{\mathrm{OCLSD}}$ is exactly the ζ zero heights) — that
stays the Hilbert–Pólya obligation, un-inhabited.
-/

namespace BEDC.Derived.RHRoute.OCLSDHamiltonian

open BEDC.Derived.RHRoute.OCLSDSpectral
open BEDC.Derived.RHRoute.LocatedGenerationTower
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

universe u

/-- Diagonal-on-orthonormal-basis Hilbert kit (mathlib-free): an operator carrier
with `SelfAdjoint` / `Unitary` predicates, a diagonal constructor from real
eigenvalues, a phase-flow constructor, and the two structural certificates a
diagonal ONB operator satisfies — a diagonal operator with REAL eigenvalues is
self-adjoint, and its phase flow is unitary. The carrier discharges these (Setup
path); no complex Hilbert space is imported. -/
structure DiagonalHilbertKit (Height : Type u) where
  Op : Type u
  SelfAdjoint : Op → Type u
  Unitary : Op → Type u
  diag : (Basis : Type u) → (Basis → Height) → Op
  phaseFlow : (Basis : Type u) → (Basis → Height) → Height → Op
  diag_selfAdjoint : (Basis : Type u) → (eigen : Basis → Height) →
    SelfAdjoint (diag Basis eigen)
  phaseFlow_unitary : (Basis : Type u) → (eigen : Basis → Height) → (τ : Height) →
    Unitary (phaseFlow Basis eigen τ)

variable {sig : RHFreeZeroSignature} {LR : Type u}
  {M : LocatedZeroModel sig LR} {K : DynamicsTypes}

/-- $H_{\mathrm{OCLSD}}$: the diagonal operator whose orthonormal basis is the forward
orbits and whose eigenvalue on orbit `o` is its cumulative angular height. -/
noncomputable def hamiltonianOp (D : GenerationDynamics M K) (C : TickHeightKit K)
    (HK : DiagonalHilbertKit C.Height) : HK.Op :=
  HK.diag (OrbitBasis D) (fun b => orbitHeight C b.orbit)

/-- $H_{\mathrm{OCLSD}}$ is self-adjoint: its eigenvalues are the located-REAL orbit
heights, so the diagonal-ONB certificate applies. ζ-free. -/
noncomputable def hamiltonian_selfAdjoint (D : GenerationDynamics M K)
    (C : TickHeightKit K) (HK : DiagonalHilbertKit C.Height) :
    HK.SelfAdjoint (hamiltonianOp D C HK) :=
  HK.diag_selfAdjoint (OrbitBasis D) (fun b => orbitHeight C b.orbit)

/-- The OCLSD phase flow $U(\tau)=e^{i\tau H_{\mathrm{OCLSD}}}$, diagonal
$e^{i\tau h(o)}$ on each orbit. -/
noncomputable def phaseFlowOp (D : GenerationDynamics M K) (C : TickHeightKit K)
    (HK : DiagonalHilbertKit C.Height) (τ : C.Height) : HK.Op :=
  HK.phaseFlow (OrbitBasis D) (fun b => orbitHeight C b.orbit) τ

/-- The OCLSD phase flow is unitary — the tick-generated one-parameter dynamical
group whose self-adjoint generator is $H_{\mathrm{OCLSD}}$. ζ-free. -/
noncomputable def phaseFlow_unitary (D : GenerationDynamics M K)
    (C : TickHeightKit K) (HK : DiagonalHilbertKit C.Height) (τ : C.Height) :
    HK.Unitary (phaseFlowOp D C HK τ) :=
  HK.phaseFlow_unitary (OrbitBasis D) (fun b => orbitHeight C b.orbit) τ

end BEDC.Derived.RHRoute.OCLSDHamiltonian
