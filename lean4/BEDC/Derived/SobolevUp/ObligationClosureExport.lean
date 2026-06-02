import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_obligation_closure_export [AskSetup] [PackageSetup]
    {D M V L G H C P N weakRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier D M V L G H C P N bundle pkg ->
      Cont L G weakRead ->
        Cont weakRead C boundaryRead ->
          PkgSig bundle boundaryRead pkg ->
            UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory V ∧ UnaryHistory L ∧
              UnaryHistory G ∧ UnaryHistory weakRead ∧ UnaryHistory boundaryRead ∧
                Cont L G weakRead ∧ Cont weakRead C boundaryRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier weakRoute boundaryRoute boundaryPkg
  rcases carrier with
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
      _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, _domainBaseCodomain,
      _codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
      provenancePkg⟩
  have weakUnary : UnaryHistory weakRead :=
    unary_cont_closed magnitudeUnary gradientUnary weakRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed weakUnary routesUnary boundaryRoute
  exact
    ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary, weakUnary,
      boundaryUnary, weakRoute, boundaryRoute, provenancePkg, boundaryPkg⟩

end BEDC.Derived.SobolevUp
