import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_analytic_operation_boundary [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      etaFunctionalRead applicationRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta functional etaFunctionalRead →
        Cont etaFunctionalRead application applicationRead →
          Cont applicationRead provenance publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory etaFunctionalRead ∧ UnaryHistory applicationRead ∧
                UnaryHistory publicRead ∧ hsame etaFunctionalRead application ∧
                  Cont etaFunctionalRead application applicationRead ∧
                    Cont applicationRead provenance publicRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier etaFunctionalRoute applicationRoute publicRoute publicPkg
  obtain ⟨etaUnary, functionalUnary, _poleUnary, _zeroLedgerUnary, _gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, carrierApplicationRoute, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have etaFunctionalUnary : UnaryHistory etaFunctionalRead :=
    unary_cont_closed etaUnary functionalUnary etaFunctionalRoute
  have sameEtaFunctionalApplication : hsame etaFunctionalRead application :=
    cont_deterministic etaFunctionalRoute carrierApplicationRoute
  have applicationReadUnary : UnaryHistory applicationRead :=
    unary_cont_closed etaFunctionalUnary applicationUnary applicationRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed applicationReadUnary provenanceUnary publicRoute
  exact
    ⟨etaFunctionalUnary, applicationReadUnary, publicReadUnary,
      sameEtaFunctionalApplication, applicationRoute, publicRoute, provenancePkg,
      publicPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
