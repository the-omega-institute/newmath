import BEDC.Derived.UpcrossingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UpcrossingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Upcrossing_finite_ledger_induction_boundary [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert lowerHit upperHit completed :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert bundle pkg →
      Cont window threshold lowerHit →
        Cont lowerHit threshold upperHit →
          Cont lowerHit upperHit completed →
            PkgSig bundle completed pkg →
              UnaryHistory lowerHit ∧ UnaryHistory upperHit ∧ UnaryHistory completed ∧
                Cont window threshold lowerHit ∧ Cont lowerHit threshold upperHit ∧
                  Cont lowerHit upperHit completed ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle completed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lowerCont upperCont completedCont completedPkg
  obtain ⟨_sourceUnary, _martingaleUnary, windowUnary, thresholdUnary, _routeUnary,
    _provenanceUnary, _localCertUnary, provenancePkg⟩ := carrier
  have lowerUnary : UnaryHistory lowerHit :=
    unary_cont_closed windowUnary thresholdUnary lowerCont
  have upperUnary : UnaryHistory upperHit :=
    unary_cont_closed lowerUnary thresholdUnary upperCont
  have completedUnary : UnaryHistory completed :=
    unary_cont_closed lowerUnary upperUnary completedCont
  exact
    ⟨lowerUnary, upperUnary, completedUnary, lowerCont, upperCont, completedCont,
      provenancePkg, completedPkg⟩

end BEDC.Derived.UpcrossingUp
