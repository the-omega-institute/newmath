import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.PrimeSkewDefect
import BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy

namespace BEDC.Derived.RHRoute.SpectralRigidityRoute

open BEDC.Derived.RHRoute.PrimeSkewDefect
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy

universe u v

-- 这里的 spectral 只是路线标签; kernel 端只记录有限 carrier、prime-window channel
-- 与递归零点层。
abbrev CriticalStripPoint : Type :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.RatComplex

-- `FixedHalfSection` is definitionally the `ConstructiveRH` target with a
-- route-local name for the source point.  It is a renamed projection surface,
-- not an independent derivation of an RH conclusion.
def FixedHalfSection : Prop :=
  ∀ point : CriticalStripPoint,
    BEDC.Derived.RHRoute.ConstructiveRHStatement.NontrivialZetaZero point ->
      BEDC.Derived.RHRoute.ConstructiveRHStatement.OnCriticalLine point

-- This theorem unfolds the two definitions and projects the same field data.
-- It should be read as a renaming/readback lemma, not as a spectral proof.
theorem fixedHalfSection_reads_constructiveRH :
    FixedHalfSection ↔
      BEDC.Derived.RHRoute.ConstructiveRHStatement.ConstructiveRH := by
  constructor
  · intro fixedSection
    intro point zero
    exact fixedSection point zero
  · intro rh
    intro point zero
    exact rh point zero

def OffCriticalLine (point : CriticalStripPoint) : Prop :=
  Not (BEDC.Derived.RHRoute.ConstructiveRHStatement.OnCriticalLine point)

structure OffLineNontrivialZero where
  point : CriticalStripPoint
  zero :
    BEDC.Derived.RHRoute.ConstructiveRHStatement.NontrivialZetaZero point
  off_line : OffCriticalLine point

theorem fixedHalfSection_excludes_off_line
    (fixedSection : FixedHalfSection) (zero : OffLineNontrivialZero) : False := by
  exact zero.off_line (fixedSection zero.point zero.zero)

structure RecursiveSpectralThread
    (signature : RHFreeZeroSignature) where
  generated : GeneratedZero signature
  layer : SpectralZeroLayer signature
  layer_readback : forgetToGeneratedZero layer = generated

def baseRecursiveSpectralThread {signature : RHFreeZeroSignature}
    (zero : GeneratedZero signature) :
    RecursiveSpectralThread signature where
  generated := zero
  layer := SpectralZeroLayer.base zero
  layer_readback := rfl

def towerRecursiveSpectralThread {signature : RHFreeZeroSignature}
    (fuel : Nat) (zero : GeneratedZero signature) :
    RecursiveSpectralThread signature where
  generated := towerReadbackGenerated fuel zero
  layer := towerReadbackLayer fuel zero
  layer_readback := towerReadbackLayer_forget fuel zero

theorem recursiveSpectralThread_readback
    {signature : RHFreeZeroSignature}
    (thread : RecursiveSpectralThread signature) :
    forgetToGeneratedZero thread.layer = thread.generated :=
  thread.layer_readback

-- Honest condition interface: `GlobalSpectralRigidity` records the two
-- assumptions needed for the prime-defect exclusion route.  It is not itself
-- the fixed-half conclusion, and the route's RH readback below comes from the
-- separate `fixed_half_section` field.
structure GlobalSpectralRigidity
    (I : PrimeSkewDefectInterface) where
  boundary_faithfulness : BoundaryFaithfulness I
  defect_zero_incompatibility : PrimeDefectZeroIncompatibility I

def offLineBoundary_to_prime_defect
    {I : PrimeSkewDefectInterface}
    (obligation : OffLineZeroBoundaryObligation I)
    (faithful : BoundaryFaithfulness I)
    (zero : obligation.off_line_zero) :
    PrimeDefect I.bulk (obligation.locate zero) := by
  exact faithful.detects (obligation.locate zero)
    (obligation.zero_atom_at zero)
    (obligation.off_line_to_prime_skew_boundary_obligation zero)

theorem offLineBoundary_defect_zero_incompatible
    {I : PrimeSkewDefectInterface}
    (obligation : OffLineZeroBoundaryObligation I)
    (faithful : BoundaryFaithfulness I)
    (incompatible : PrimeDefectZeroIncompatibility I)
    (zero : obligation.off_line_zero) : False := by
  exact incompatible (obligation.locate zero)
    (obligation.zero_atom_at zero)
    (offLineBoundary_to_prime_defect obligation faithful zero)

theorem globalSpectralRigidity_excludes_off_line
    {I : PrimeSkewDefectInterface}
    (obligation : OffLineZeroBoundaryObligation I)
    (rigidity : GlobalSpectralRigidity I)
    (zero : obligation.off_line_zero) : False := by
  exact offLineBoundary_defect_zero_incompatible obligation
    rigidity.boundary_faithfulness rigidity.defect_zero_incompatibility zero

structure SpectralRigidityRoute
    (I : PrimeSkewDefectInterface) where
  signature : RHFreeZeroSignature
  thread : RecursiveSpectralThread signature
  fixed_half_section : FixedHalfSection
  off_line_boundary : OffLineZeroBoundaryObligation I
  global_rigidity : GlobalSpectralRigidity I

theorem spectralRigidityRoute_thread_readback
    {I : PrimeSkewDefectInterface}
    (route : SpectralRigidityRoute I) :
    forgetToGeneratedZero route.thread.layer = route.thread.generated :=
  route.thread.layer_readback

-- Field projection through `FixedHalfSection`; the global rigidity assumptions
-- are not used to derive this `ConstructiveRH` readback.
theorem spectralRigidityRoute_reads_constructiveRH
    {I : PrimeSkewDefectInterface}
    (route : SpectralRigidityRoute I) :
    BEDC.Derived.RHRoute.ConstructiveRHStatement.ConstructiveRH := by
  exact fixedHalfSection_reads_constructiveRH.mp route.fixed_half_section

theorem spectralRigidityRoute_excludes_constructive_off_line
    {I : PrimeSkewDefectInterface}
    (route : SpectralRigidityRoute I)
    (zero : OffLineNontrivialZero) : False := by
  exact fixedHalfSection_excludes_off_line route.fixed_half_section zero

theorem spectralRigidityRoute_excludes_off_line
    {I : PrimeSkewDefectInterface}
    (route : SpectralRigidityRoute I)
    (zero : route.off_line_boundary.off_line_zero) : False := by
  exact globalSpectralRigidity_excludes_off_line route.off_line_boundary
    route.global_rigidity zero

theorem conditionalSpectralRigidity_excludes_off_line
    {I : PrimeSkewDefectInterface}
    (obligation : OffLineZeroBoundaryObligation I)
    (rigidity : GlobalSpectralRigidity I)
    (zero : obligation.off_line_zero) : False := by
  exact globalSpectralRigidity_excludes_off_line obligation rigidity zero

end BEDC.Derived.RHRoute.SpectralRigidityRoute
