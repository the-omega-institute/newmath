import BEDC.Derived.LocatedSupremumUp.Carrier

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSupremumCarrier_monotone_convergence_consumer_envelope [AskSetup]
    [PackageSetup] {L U A W R E H C P N completionRoute classifierBoundary stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedSupremumCarrier L U A W R E H C P N bundle pkg ->
      Cont R E completionRoute ->
        Cont completionRoute H classifierBoundary ->
          Cont classifierBoundary C stableRead ->
            PkgSig bundle classifierBoundary pkg ->
              PkgSig bundle stableRead pkg ->
                UnaryHistory completionRoute ∧ UnaryHistory classifierBoundary ∧
                  UnaryHistory stableRead ∧ Cont R E completionRoute ∧
                    Cont completionRoute H classifierBoundary ∧
                      Cont classifierBoundary C stableRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg ∧ PkgSig bundle stableRead pkg := by
  -- BEDC touchpoint anchor: LocatedSupremumCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier completionRouteCont classifierBoundaryCont stableReadCont _classifierBoundaryPkg
    stableReadPkg
  obtain ⟨unaryR, unaryA, carrierSealCont, _sameLU, unaryW, carrierReplayCont,
    sameH, provenancePkg, _sameN, localNamePkg⟩ := carrier
  have unaryE : UnaryHistory E :=
    unary_cont_closed unaryR unaryA carrierSealCont
  have completionRouteUnary : UnaryHistory completionRoute :=
    unary_cont_closed unaryR unaryE completionRouteCont
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryW unaryR carrierReplayCont
  have unaryH : UnaryHistory H :=
    unary_cont_closed unaryC unaryW sameH
  have classifierBoundaryUnary : UnaryHistory classifierBoundary :=
    unary_cont_closed completionRouteUnary unaryH classifierBoundaryCont
  have stableReadUnary : UnaryHistory stableRead :=
    unary_cont_closed classifierBoundaryUnary unaryC stableReadCont
  exact
    ⟨completionRouteUnary, classifierBoundaryUnary, stableReadUnary, completionRouteCont,
      classifierBoundaryCont, stableReadCont, provenancePkg, localNamePkg, stableReadPkg⟩

end BEDC.Derived.LocatedSupremumUp
