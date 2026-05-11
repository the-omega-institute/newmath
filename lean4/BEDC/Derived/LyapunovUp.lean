import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LyapunovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LyapunovLedger [AskSetup] [PackageSetup]
    (state transition quadratic positive decrease transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory quadratic ∧
    UnaryHistory positive ∧ UnaryHistory decrease ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont state transition positive ∧ Cont quadratic positive decrease ∧
          Cont decrease route transport ∧ Cont transport provenance name ∧
            PkgSig bundle name pkg

theorem LyapunovLedger_stability_transport [AskSetup] [PackageSetup]
    {state transition quadratic positive decrease transport route provenance name state'
      transition' quadratic' positive' decrease' transport' route' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovLedger state transition quadratic positive decrease transport route provenance name
        bundle pkg ->
      hsame state state' -> hsame transition transition' -> hsame quadratic quadratic' ->
        hsame positive positive' -> hsame decrease decrease' -> hsame route route' ->
          hsame provenance provenance' -> Cont state' transition' positive' ->
            Cont quadratic' positive' decrease' -> Cont decrease' route' transport' ->
              Cont transport' provenance' name' -> PkgSig bundle name' pkg ->
                LyapunovLedger state' transition' quadratic' positive' decrease' transport'
                    route' provenance' name' bundle pkg ∧
                  hsame transport transport' ∧ hsame name name' := by
  intro ledger sameState sameTransition sameQuadratic samePositive sameDecrease sameRoute
    sameProvenance positiveCont' decreaseCont' transportCont' nameCont' pkgSig'
  have stateUnary' : UnaryHistory state' :=
    unary_transport ledger.left sameState
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport ledger.right.left sameTransition
  have quadraticUnary' : UnaryHistory quadratic' :=
    unary_transport ledger.right.right.left sameQuadratic
  have positiveUnary' : UnaryHistory positive' :=
    unary_transport ledger.right.right.right.left samePositive
  have decreaseUnary' : UnaryHistory decrease' :=
    unary_transport ledger.right.right.right.right.left sameDecrease
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameDecrease sameRoute
      ledger.right.right.right.right.right.right.right.right.right.right.right.left
      transportCont'
  have transportUnary' : UnaryHistory transport' :=
    unary_transport ledger.right.right.right.right.right.left sameTransport
  have routeUnary' : UnaryHistory route' :=
    unary_transport ledger.right.right.right.right.right.right.left sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport ledger.right.right.right.right.right.right.right.left sameProvenance
  have sameName : hsame name name' :=
    cont_respects_hsame sameTransport sameProvenance
      ledger.right.right.right.right.right.right.right.right.right.right.right.right.left
      nameCont'
  have nameUnary' : UnaryHistory name' :=
    unary_transport ledger.right.right.right.right.right.right.right.right.left sameName
  exact And.intro
    (And.intro stateUnary'
      (And.intro transitionUnary'
        (And.intro quadraticUnary'
          (And.intro positiveUnary'
            (And.intro decreaseUnary'
              (And.intro transportUnary'
                (And.intro routeUnary'
                  (And.intro provenanceUnary'
                    (And.intro nameUnary'
                      (And.intro positiveCont'
                        (And.intro decreaseCont'
                          (And.intro transportCont'
                            (And.intro nameCont' pkgSig')))))))))))))
    (And.intro sameTransport sameName)

end BEDC.Derived.LyapunovUp
