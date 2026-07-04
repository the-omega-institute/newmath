import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.PrimeSkewDefect
import BEDC.Derived.RHRoute.SpectralRigidityRoute

namespace BEDC.Derived.RHRoute.CriticalLineLocator

open BEDC.Derived.RHRoute.PrimeSkewDefect
open BEDC.Derived.RHRoute.SpectralRigidityRoute

universe u v

abbrev CriticalStripPoint :=
  BEDC.Derived.RHRoute.SpectralRigidityRoute.CriticalStripPoint

abbrev NontrivialZetaZero :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.NontrivialZetaZero

abbrev OnCriticalLine :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.OnCriticalLine

abbrev ConstructiveRH :=
  BEDC.Derived.RHRoute.ConstructiveRHStatement.ConstructiveRH

def CriticalLineLocator : Type :=
  (point : CriticalStripPoint) ->
    NontrivialZetaZero point ->
      Decidable (OnCriticalLine point)

structure ConstructiveOffLineBoundaryRepresentation
    (I : PrimeSkewDefectInterface.{u, v})
    (obligation : OffLineZeroBoundaryObligation I) where
  toBoundary :
    (point : CriticalStripPoint) ->
      NontrivialZetaZero point ->
        Not (OnCriticalLine point) ->
          obligation.off_line_zero

def boundaryZeroOfConstructiveOffLine
    {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (representation :
      ConstructiveOffLineBoundaryRepresentation I obligation)
    (zero : OffLineNontrivialZero) :
    obligation.off_line_zero :=
  representation.toBoundary zero.point zero.zero zero.off_line

theorem constructiveOffLine_refuted_by_globalRigidity
    {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (representation :
      ConstructiveOffLineBoundaryRepresentation I obligation)
    (rigidity : GlobalSpectralRigidity I)
    (zero : OffLineNontrivialZero) : False := by
  exact globalSpectralRigidity_excludes_off_line obligation rigidity
    (boundaryZeroOfConstructiveOffLine representation zero)

theorem constructiveOffLine_refuted_by_boundary_conditions
    {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (representation :
      ConstructiveOffLineBoundaryRepresentation I obligation)
    (faithful : BoundaryFaithfulness I)
    (incompatible : PrimeDefectZeroIncompatibility I)
    (zero : OffLineNontrivialZero) : False := by
  let rigidity : GlobalSpectralRigidity I :=
    { boundary_faithfulness := faithful
      defect_zero_incompatibility := incompatible }
  exact constructiveOffLine_refuted_by_globalRigidity representation rigidity zero

abbrev OffLineZeroType : Type :=
  OffLineNontrivialZero

theorem offLineZeroType_empty_from_globalRigidity
    {I : PrimeSkewDefectInterface.{u, v}}
    {obligation : OffLineZeroBoundaryObligation I}
    (representation :
      ConstructiveOffLineBoundaryRepresentation I obligation)
    (rigidity : GlobalSpectralRigidity I) :
    OffLineZeroType -> False := by
  intro zero
  exact constructiveOffLine_refuted_by_globalRigidity representation rigidity zero

theorem criticalLineLocator_to_constructiveRH
    {I : PrimeSkewDefectInterface.{u, v}}
    (locator : CriticalLineLocator)
    (obligation : OffLineZeroBoundaryObligation I)
    (representation :
      ConstructiveOffLineBoundaryRepresentation I obligation)
    (rigidity : GlobalSpectralRigidity I) :
    ConstructiveRH := by
  intro point zero
  cases locator point zero with
  | isTrue onLine =>
      exact onLine
  | isFalse offLine =>
      exact False.elim
        (globalSpectralRigidity_excludes_off_line obligation rigidity
          (representation.toBoundary point zero offLine))

theorem criticalLineLocator_with_faithfulness_to_constructiveRH
    {I : PrimeSkewDefectInterface.{u, v}}
    (locator : CriticalLineLocator)
    (obligation : OffLineZeroBoundaryObligation I)
    (representation :
      ConstructiveOffLineBoundaryRepresentation I obligation)
    (faithful : BoundaryFaithfulness I)
    (incompatible : PrimeDefectZeroIncompatibility I) :
    ConstructiveRH := by
  let rigidity : GlobalSpectralRigidity I :=
    { boundary_faithfulness := faithful
      defect_zero_incompatibility := incompatible }
  exact criticalLineLocator_to_constructiveRH locator obligation
    representation rigidity

theorem criticalLineLocator_to_fixedHalfSection
    {I : PrimeSkewDefectInterface.{u, v}}
    (locator : CriticalLineLocator)
    (obligation : OffLineZeroBoundaryObligation I)
    (representation :
      ConstructiveOffLineBoundaryRepresentation I obligation)
    (rigidity : GlobalSpectralRigidity I) :
    FixedHalfSection := by
  exact fixedHalfSection_reads_constructiveRH.mpr
    (criticalLineLocator_to_constructiveRH locator obligation
      representation rigidity)

end BEDC.Derived.RHRoute.CriticalLineLocator
