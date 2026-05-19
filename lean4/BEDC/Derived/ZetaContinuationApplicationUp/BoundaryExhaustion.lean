import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_boundary_exhaustion [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name sourceRead
      routeRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont eta gamma sourceRead →
        Cont sourceRead application routeRead →
          Cont routeRead provenance boundaryRead →
            PkgSig bundle boundaryRead pkg →
              UnaryHistory pole ∧ UnaryHistory zeroLedger ∧ UnaryHistory gamma ∧
                UnaryHistory application ∧ UnaryHistory sourceRead ∧ UnaryHistory routeRead ∧
                  UnaryHistory boundaryRead ∧ Cont eta gamma sourceRead ∧
                    Cont sourceRead application routeRead ∧
                      Cont routeRead provenance boundaryRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier etaGammaSource sourceApplicationRoute routeProvenanceBoundary boundaryPkg
  obtain ⟨etaUnary, _functionalUnary, poleUnary, zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed etaUnary gammaUnary etaGammaSource
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sourceReadUnary applicationUnary sourceApplicationRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed routeReadUnary provenanceUnary routeProvenanceBoundary
  exact
    ⟨poleUnary, zeroLedgerUnary, gammaUnary, applicationUnary, sourceReadUnary,
      routeReadUnary, boundaryReadUnary, etaGammaSource, sourceApplicationRoute,
      routeProvenanceBoundary, provenancePkg, boundaryPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
