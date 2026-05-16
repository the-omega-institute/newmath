import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_primitive_scope [AskSetup] [PackageSetup]
    {B S W D R E H C P N primitiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont C N primitiveRead ->
        PkgSig bundle primitiveRead pkg ->
          UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
            UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory C ∧ UnaryHistory N ∧
              UnaryHistory primitiveRead ∧ Cont B S W ∧ Cont W D R ∧ Cont R E C ∧
                Cont C N primitiveRead ∧ hsame N E ∧
                  PkgSig bundle primitiveRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier primitiveRoute primitivePkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute, sealRoute,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryR unaryE sealRoute
  have unaryN : UnaryHistory N :=
    unary_transport_symm unaryE sameName
  have unaryPrimitiveRead : UnaryHistory primitiveRead :=
    unary_cont_closed unaryC unaryN primitiveRoute
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryC, unaryN,
      unaryPrimitiveRead, budgetRoute, regularRoute, sealRoute, primitiveRoute, sameName,
      primitivePkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
