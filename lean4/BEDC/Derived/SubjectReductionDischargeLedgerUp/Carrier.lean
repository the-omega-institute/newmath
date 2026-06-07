import BEDC.Derived.SubjectReductionDischargeLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionDischargeLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubjectReductionDischargeLedgerCarrier [AskSetup] [PackageSetup]
    (beta appArg lambdaDomain piDomain route transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lambdaDomain ∧
    UnaryHistory piDomain ∧ UnaryHistory route ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont beta appArg route ∧ Cont lambdaDomain piDomain replay ∧
          Cont route transport provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem SubjectReductionDischargeLedgerCarrier_route_handoff [AskSetup] [PackageSetup]
    {beta appArg lambdaDomain piDomain route transport replay provenance name routeRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeLedgerCarrier beta appArg lambdaDomain piDomain route
        transport replay provenance name bundle pkg →
      Cont route replay routeRead →
        Cont routeRead transport replayRead →
          PkgSig bundle replayRead pkg →
            UnaryHistory route ∧ UnaryHistory replay ∧ UnaryHistory transport ∧
              UnaryHistory routeRead ∧ UnaryHistory replayRead ∧
                Cont beta appArg route ∧ Cont lambdaDomain piDomain replay ∧
                  Cont route replay routeRead ∧ Cont routeRead transport replayRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier routeReplay routeTransport replayPkg
  obtain ⟨_unaryBeta, _unaryAppArg, _unaryLambdaDomain, _unaryPiDomain, unaryRoute,
    unaryTransport, unaryReplay, _unaryProvenance, _unaryName, betaRoute, lambdaReplay,
    _routeTransport, provenancePkg, _namePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryRoute unaryReplay routeReplay
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed routeReadUnary unaryTransport routeTransport
  exact
    ⟨unaryRoute, unaryReplay, unaryTransport, routeReadUnary, replayReadUnary,
      betaRoute, lambdaReplay, routeReplay, routeTransport, provenancePkg, replayPkg⟩

end BEDC.Derived.SubjectReductionDischargeLedgerUp
