import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_gamma_eta_handoff [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name sourceRead
      gammaRead supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont gamma application gammaRead →
          Cont gammaRead provenance supportRead →
            PkgSig bundle supportRead pkg →
              UnaryHistory eta ∧ UnaryHistory gamma ∧ UnaryHistory application ∧
                UnaryHistory provenance ∧ UnaryHistory sourceRead ∧ UnaryHistory gammaRead ∧
                  UnaryHistory supportRead ∧ Cont eta gamma sourceRead ∧
                    Cont gamma application gammaRead ∧ Cont gammaRead provenance supportRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle supportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier etaGammaSource gammaApplicationRead gammaReadProvenanceSupport supportPkg
  obtain ⟨etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed gammaReadUnary provenanceUnary gammaReadProvenanceSupport
  exact
    ⟨etaUnary, gammaUnary, applicationUnary, provenanceUnary, sourceReadUnary,
      gammaReadUnary, supportReadUnary, etaGammaSource, gammaApplicationRead,
      gammaReadProvenanceSupport, provenancePkg, supportPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
