import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCompletionConsumerBoundary [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert
      completionRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      Cont ledger sealRow completionRead ->
        Cont completionRead transport replayRead ->
          PkgSig bundle replayRead pkg ->
            Cont ledger (append sealRow transport) replayRead ∧
              UnaryHistory completionRead ∧ UnaryHistory replayRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier completionRoute replayRoute replayPkg
  obtain ⟨_tailUnary, _modulusUnary, _toleranceUnary, ledgerUnary, sealUnary,
    transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed ledgerUnary sealUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary transportUnary replayRoute
  have composedRoute : Cont ledger (append sealRow transport) replayRead := by
    cases completionRoute
    cases replayRoute
    exact append_assoc ledger sealRow transport
  exact ⟨composedRoute, completionUnary, replayUnary, provenancePkg, replayPkg⟩

end BEDC.Derived.CauchyOscillationUp
