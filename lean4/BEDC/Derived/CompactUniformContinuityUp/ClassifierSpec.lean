import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def CompactUniformContinuityClassifierSpec [AskSetup] [PackageSetup]
    (source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow source' target' graph' tolerance' precision' net' coverage' modulusRows'
      radiusRows' fold' transport' route' nameRow' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CompactUniformContinuityPacket source target graph tolerance precision net coverage
      modulusRows radiusRows fold transport route nameRow bundle pkg ∧
    CompactUniformContinuityPacket source' target' graph' tolerance' precision' net' coverage'
      modulusRows' radiusRows' fold' transport' route' nameRow' bundle pkg ∧
      hsame source source' ∧ hsame target target' ∧ hsame graph graph' ∧
        hsame tolerance tolerance' ∧ hsame precision precision' ∧ hsame net net' ∧
          hsame coverage coverage' ∧ hsame modulusRows modulusRows' ∧
            hsame radiusRows radiusRows' ∧ hsame fold fold' ∧ hsame transport transport' ∧
              hsame route route' ∧ hsame nameRow nameRow'

theorem CompactUniformContinuityPacket_classifier_symmetric [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow source' target' graph' tolerance' precision' net' coverage' modulusRows'
      radiusRows' fold' transport' route' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityClassifierSpec source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow source' target' graph' tolerance'
        precision' net' coverage' modulusRows' radiusRows' fold' transport' route' nameRow'
        bundle pkg →
      CompactUniformContinuityClassifierSpec source' target' graph' tolerance' precision' net'
        coverage' modulusRows' radiusRows' fold' transport' route' nameRow' source target graph
        tolerance precision net coverage modulusRows radiusRows fold transport route nameRow
        bundle pkg := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle Pkg
  intro classifier
  obtain ⟨leftPacket, rightPacket, sameSource, sameTarget, sameGraph, sameTolerance,
    samePrecision, sameNet, sameCoverage, sameModulusRows, sameRadiusRows, sameFold,
    sameTransport, sameRoute, sameNameRow⟩ := classifier
  exact
    ⟨rightPacket, leftPacket, hsame_symm sameSource, hsame_symm sameTarget,
      hsame_symm sameGraph, hsame_symm sameTolerance, hsame_symm samePrecision,
      hsame_symm sameNet, hsame_symm sameCoverage, hsame_symm sameModulusRows,
      hsame_symm sameRadiusRows, hsame_symm sameFold, hsame_symm sameTransport,
      hsame_symm sameRoute, hsame_symm sameNameRow⟩

end BEDC.Derived.CompactUniformContinuityUp
