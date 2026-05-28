import BEDC.Derived.UpcrossingUp.TasteGate

namespace BEDC.Derived.UpcrossingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpcrossingInequalityMartingaleConvergenceHandoff [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert routeRead handoffRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert
        bundle pkg →
      Cont martingale window routeRead →
        Cont routeRead threshold handoffRead →
          PkgSig bundle handoffRead pkg →
            UnaryHistory martingale ∧ UnaryHistory window ∧ UnaryHistory threshold ∧
              UnaryHistory routeRead ∧ UnaryHistory handoffRead ∧
                Cont martingale window routeRead ∧ Cont routeRead threshold handoffRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier martingaleWindow routeThreshold handoffPkg
  obtain ⟨_sourceUnary, martingaleUnary, windowUnary, thresholdUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, provenancePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed martingaleUnary windowUnary martingaleWindow
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed routeReadUnary thresholdUnary routeThreshold
  exact
    ⟨martingaleUnary, windowUnary, thresholdUnary, routeReadUnary, handoffReadUnary,
      martingaleWindow, routeThreshold, provenancePkg, handoffPkg⟩

end BEDC.Derived.UpcrossingUp
