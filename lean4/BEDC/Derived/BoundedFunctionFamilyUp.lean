import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedFunctionFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedFunctionFamilyCarrier [AskSetup] [PackageSetup]
    (source target index maps pointBounds supNorm transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory index ∧
    UnaryHistory maps ∧ UnaryHistory pointBounds ∧ UnaryHistory supNorm ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont source maps replay ∧
          Cont maps pointBounds supNorm ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem BoundedFunctionFamilyCarrier_sup_norm_route [AskSetup] [PackageSetup]
    {source target index maps pointBounds supNorm transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedFunctionFamilyCarrier source target index maps pointBounds supNorm transport
        replay provenance localName bundle pkg →
      UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory index ∧
        UnaryHistory maps ∧ UnaryHistory pointBounds ∧ UnaryHistory supNorm ∧
          Cont maps pointBounds supNorm ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier
  obtain ⟨sourceUnary, targetUnary, indexUnary, mapsUnary, pointBoundsUnary,
    supNormUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _sourceMapsReplay, mapsPointBoundsSupNorm, _transportReplayProvenance,
    provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨sourceUnary, targetUnary, indexUnary, mapsUnary, pointBoundsUnary, supNormUnary,
      mapsPointBoundsSupNorm, provenancePkg, localNamePkg⟩

end BEDC.Derived.BoundedFunctionFamilyUp
