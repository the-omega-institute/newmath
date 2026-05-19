import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterLeanIntakeNonescape
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow intake : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        Cont sealRow H intake ->
          PkgSig bundle intake pkg ->
            UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory Q ∧
              UnaryHistory E ∧ UnaryHistory sealRow ∧ UnaryHistory intake ∧
                Cont S D R ∧ Cont R B Q ∧ Cont Q E sealRow ∧ Cont sealRow H intake ∧
                  hsame N E ∧ PkgSig bundle intake pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg hsame
  intro carrier sealRoute intakeRoute intakePkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _unaryC, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryIntake : UnaryHistory intake :=
    unary_cont_closed unarySeal unaryH intakeRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryQ, unaryE, unarySeal, unaryIntake, routeR, routeQ,
      sealRoute, intakeRoute, sameNameSeal, intakePkg⟩

end BEDC.Derived.FiniteTailFilterUp
