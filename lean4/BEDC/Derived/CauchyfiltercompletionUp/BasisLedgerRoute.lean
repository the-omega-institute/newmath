import BEDC.Derived.CauchyfiltercompletionUp.BasisRoute

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterCompletionBasisLedgerRoute [AskSetup] [PackageSetup]
    (filter windows tolerance readback sealRow transport replay provenance name basisRead ledgerRead :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  CauchyFilterCompletionBasisRoute filter windows tolerance readback sealRow transport replay
      provenance name basisRead bundle pkg ∧
    Cont basisRead sealRow ledgerRead ∧ Cont transport replay provenance ∧
      PkgSig bundle ledgerRead pkg

theorem CauchyFilterCompletionBasisLedgerRoute_closure [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead ledgerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionBasisLedgerRoute filter windows tolerance readback sealRow transport replay
        provenance name basisRead ledgerRead bundle pkg →
      UnaryHistory basisRead ∧ UnaryHistory ledgerRead ∧ Cont basisRead sealRow ledgerRead ∧
        Cont transport replay provenance ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro route
  obtain ⟨basisRoute, basisSealLedger, transportReplayProvenance, ledgerPkg⟩ := route
  obtain ⟨packet, filterWindowsBasis, _basisToleranceReadback, _basisPkg⟩ := basisRoute
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindowsTolerance,
    _toleranceReadbackSeal, _packetTransportReplay, _provenancePkg, _namePkg⟩ := packet
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed filterUnary windowsUnary filterWindowsBasis
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed basisUnary sealUnary basisSealLedger
  exact
    ⟨basisUnary, ledgerUnary, basisSealLedger, transportReplayProvenance, ledgerPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
