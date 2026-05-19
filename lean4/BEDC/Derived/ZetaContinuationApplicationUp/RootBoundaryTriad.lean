import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_root_boundary_triad [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      gammaRoot appRoot etaRoot : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont gamma application gammaRoot →
        Cont application eta appRoot →
          Cont eta replay etaRoot →
            PkgSig bundle gammaRoot pkg →
              PkgSig bundle appRoot pkg →
                PkgSig bundle etaRoot pkg →
                  UnaryHistory gamma ∧ UnaryHistory application ∧ UnaryHistory eta ∧
                    UnaryHistory gammaRoot ∧ UnaryHistory appRoot ∧ UnaryHistory etaRoot ∧
                      Cont gamma application gammaRoot ∧ Cont application eta appRoot ∧
                        Cont eta replay etaRoot ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle gammaRoot pkg ∧ PkgSig bundle appRoot pkg ∧
                            PkgSig bundle etaRoot pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gammaApplicationRoot applicationEtaRoot etaReplayRoot gammaRootPkg appRootPkg
    etaRootPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have gammaRootUnary : UnaryHistory gammaRoot :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRoot
  have appRootUnary : UnaryHistory appRoot :=
    unary_cont_closed applicationUnary etaUnary applicationEtaRoot
  have etaRootUnary : UnaryHistory etaRoot :=
    unary_cont_closed etaUnary replayUnary etaReplayRoot
  exact
    ⟨gammaUnary, applicationUnary, etaUnary, gammaRootUnary, appRootUnary, etaRootUnary,
      gammaApplicationRoot, applicationEtaRoot, etaReplayRoot, provenancePkg, gammaRootPkg,
      appRootPkg, etaRootPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
