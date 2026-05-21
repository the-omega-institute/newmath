import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_source_lock_triad_visible_separation
    [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name etaTail
      gammaTail appTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      hsame eta (BHist.e0 etaTail) →
        hsame gamma (BHist.e1 gammaTail) →
          hsame application (BHist.e0 appTail) →
            hsame eta gamma → False := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame
  intro carrier etaVisible gammaVisible applicationVisible sameEtaGamma
  obtain ⟨_etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, _gammaUnary,
    _applicationUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    _provenancePkg, _namePkg⟩ := carrier
  have _applicationAnchor : hsame application (BHist.e0 appTail) := applicationVisible
  have visibleSame : hsame (BHist.e0 etaTail) (BHist.e1 gammaTail) :=
    hsame_trans (hsame_symm etaVisible) (hsame_trans sameEtaGamma gammaVisible)
  exact not_hsame_e0_e1 visibleSame

end BEDC.Derived.ZetaContinuationApplicationUp
