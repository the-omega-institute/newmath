import BEDC.Derived.UpcrossingUp.TasteGate

namespace BEDC.Derived.UpcrossingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpcrossingFiniteLedgerHandoff [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert lowerHit upperHit completed
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert bundle pkg →
      Cont window threshold lowerHit →
        Cont lowerHit threshold upperHit →
          Cont lowerHit upperHit completed →
            Cont completed route handoff →
              PkgSig bundle handoff pkg →
                UnaryHistory lowerHit ∧ UnaryHistory upperHit ∧ UnaryHistory completed ∧
                  UnaryHistory handoff ∧ Cont window threshold lowerHit ∧
                    Cont lowerHit threshold upperHit ∧ Cont lowerHit upperHit completed ∧
                      Cont completed route handoff ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lowerCont upperCont completedCont handoffCont handoffPkg
  obtain ⟨_sourceUnary, _martingaleUnary, windowUnary, thresholdUnary, routeUnary,
    _provenanceUnary, _localCertUnary, provenancePkg⟩ := carrier
  have lowerUnary : UnaryHistory lowerHit :=
    unary_cont_closed windowUnary thresholdUnary lowerCont
  have upperUnary : UnaryHistory upperHit :=
    unary_cont_closed lowerUnary thresholdUnary upperCont
  have completedUnary : UnaryHistory completed :=
    unary_cont_closed lowerUnary upperUnary completedCont
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed completedUnary routeUnary handoffCont
  exact
    ⟨lowerUnary, upperUnary, completedUnary, handoffUnary, lowerCont, upperCont,
      completedCont, handoffCont, provenancePkg, handoffPkg⟩

end BEDC.Derived.UpcrossingUp
