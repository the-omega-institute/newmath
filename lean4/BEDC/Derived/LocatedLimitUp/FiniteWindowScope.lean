import BEDC.Derived.LocatedLimitUp.RealSealRoute

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedLimitCarrier_finite_window_scope [AskSetup] [PackageSetup]
    {S M T Q E H C P N windowRead toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedLimitCarrier S M T Q E H C P N bundle pkg ->
      Cont S T windowRead ->
        Cont M T toleranceRead ->
          UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory Q ∧
            UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory windowRead ∧
              UnaryHistory toleranceRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory LocatedLimitCarrier
  intro carrier windowRoute toleranceRoute
  obtain ⟨unaryS, unaryM, unaryT, unaryQ, unaryE, unaryH, unaryC, _unaryP, _unaryN,
    provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryS unaryT windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryM unaryT toleranceRoute
  exact
    ⟨unaryS, unaryM, unaryT, unaryQ, unaryE, unaryH, unaryC, windowUnary,
      toleranceUnary, provenancePkg⟩

end BEDC.Derived.LocatedLimitUp
