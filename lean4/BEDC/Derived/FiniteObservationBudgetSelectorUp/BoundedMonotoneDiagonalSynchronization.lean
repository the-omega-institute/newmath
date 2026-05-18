import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_bounded_monotone_diagonal_synchronization
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N bmSelector bmSeal diagonalSeal diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E bmSelector ->
        Cont bmSelector E bmSeal ->
          Cont R E diagonalSeal ->
            Cont diagonalSeal bmSeal diagonalRead ->
              PkgSig bundle bmSeal pkg ->
                PkgSig bundle diagonalRead pkg ->
                  UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
                    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory bmSelector ∧
                      UnaryHistory bmSeal ∧ UnaryHistory diagonalSeal ∧
                        UnaryHistory diagonalRead ∧ Cont B S W ∧ Cont W D R ∧
                          Cont R E bmSelector ∧ Cont bmSelector E bmSeal ∧
                            Cont R E diagonalSeal ∧ Cont diagonalSeal bmSeal diagonalRead ∧
                              hsame N E ∧ PkgSig bundle bmSeal pkg ∧
                                PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier bmSelectorRoute bmSealRoute diagonalSealRoute diagonalReadRoute bmPkg
    diagonalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, routeW, routeR, _routeC,
    sameEndpoint⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryBmSelector : UnaryHistory bmSelector :=
    unary_cont_closed unaryR unaryE bmSelectorRoute
  have unaryBmSeal : UnaryHistory bmSeal :=
    unary_cont_closed unaryBmSelector unaryE bmSealRoute
  have unaryDiagonalSeal : UnaryHistory diagonalSeal :=
    unary_cont_closed unaryR unaryE diagonalSealRoute
  have unaryDiagonalRead : UnaryHistory diagonalRead :=
    unary_cont_closed unaryDiagonalSeal unaryBmSeal diagonalReadRoute
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryBmSelector, unaryBmSeal,
      unaryDiagonalSeal, unaryDiagonalRead, routeW, routeR, bmSelectorRoute,
      bmSealRoute, diagonalSealRoute, diagonalReadRoute, sameEndpoint, bmPkg, diagonalPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
