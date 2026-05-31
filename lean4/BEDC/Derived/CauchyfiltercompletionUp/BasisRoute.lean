import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterCompletionBasisRoute [AskSetup] [PackageSetup]
    (filter windows tolerance readback sealRow transport replay provenance name basisRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay provenance
      name bundle pkg ∧
    Cont filter windows basisRead ∧ Cont basisRead tolerance readback ∧
      PkgSig bundle basisRead pkg

theorem CauchyFilterCompletionBasisRoute_closure [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionBasisRoute filter windows tolerance readback sealRow transport replay
        provenance name basisRead bundle pkg →
      UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory basisRead ∧
        UnaryHistory readback ∧ Cont filter windows basisRead ∧
          Cont basisRead tolerance readback ∧ PkgSig bundle basisRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro route
  obtain ⟨packet, filterWindowsBasis, basisToleranceReadback, basisPkg⟩ := route
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindowsTolerance,
    _toleranceReadbackSeal, _transportReplayProvenance, _provenancePkg, _namePkg⟩ := packet
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed filterUnary windowsUnary filterWindowsBasis
  exact
    ⟨filterUnary, windowsUnary, basisUnary, readbackUnary, filterWindowsBasis,
      basisToleranceReadback, basisPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
