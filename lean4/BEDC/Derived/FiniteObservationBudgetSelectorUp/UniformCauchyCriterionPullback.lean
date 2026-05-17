import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_uniform_cauchycriterion_pullback
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N WU QU TU EU pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont WU QU TU →
        Cont TU EU pullbackRead →
          hsame W WU →
            hsame D QU →
              hsame R TU →
                hsame E EU →
                  PkgSig bundle pullbackRead pkg →
                    UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
                      UnaryHistory E ∧ UnaryHistory pullbackRead ∧ Cont WU QU TU ∧
                        Cont TU EU pullbackRead ∧ hsame W WU ∧ hsame D QU ∧
                          hsame R TU ∧ hsame E EU ∧
                            PkgSig bundle pullbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier uniformTail uniformSeal sameWindow sameDyadic sameRegular sameEndpoint
    pullbackPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute,
    _sealRoute, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have unaryTU : UnaryHistory TU :=
    unary_transport unaryR sameRegular
  have unaryEU : UnaryHistory EU :=
    unary_transport unaryE sameEndpoint
  have unaryPullback : UnaryHistory pullbackRead :=
    unary_cont_closed unaryTU unaryEU uniformSeal
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unaryPullback, uniformTail, uniformSeal,
      sameWindow, sameDyadic, sameRegular, sameEndpoint, pullbackPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
