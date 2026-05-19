import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_complete_metric_no_choice_interface
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead terminal completionA
      completionB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont u v t ->
        Cont t w selected ->
          Cont selected q readback ->
            Cont readback e sealRead ->
              Cont sealRead h terminal ->
                Cont terminal c completionA ->
                  Cont terminal c completionB ->
                    PkgSig bundle completionA pkg ->
                      PkgSig bundle completionB pkg ->
                        hsame completionA completionB /\ UnaryHistory terminal /\
                          UnaryHistory completionA /\ UnaryHistory completionB /\
                            PkgSig bundle p pkg /\ PkgSig bundle completionA pkg /\
                              PkgSig bundle completionB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier _uvt selectedRoute readbackRoute sealRoute terminalRoute completionRouteA
    completionRouteB completionPkgA completionPkgB
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
      hUnary, cUnary, _pUnary, _nUnary, _m0m1u, _carrierUvt, _twq, _qeh,
      pPkg, _hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealReadUnary hUnary terminalRoute
  have completionUnaryA : UnaryHistory completionA :=
    unary_cont_closed terminalUnary cUnary completionRouteA
  have completionUnaryB : UnaryHistory completionB :=
    unary_cont_closed terminalUnary cUnary completionRouteB
  have sameCompletion : hsame completionA completionB :=
    cont_deterministic completionRouteA completionRouteB
  exact
    ⟨sameCompletion, terminalUnary, completionUnaryA, completionUnaryB, pPkg,
      completionPkgA, completionPkgB⟩

theorem CauchyModulusRefinementCompleteMetricNoChoiceInterface [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n terminal completionA completionB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c terminal ->
        Cont terminal c completionA ->
          Cont terminal c completionB ->
            PkgSig bundle completionA pkg ->
              PkgSig bundle completionB pkg ->
                hsame completionA completionB ∧ UnaryHistory terminal ∧
                  UnaryHistory completionA ∧ UnaryHistory completionB ∧
                    PkgSig bundle completionA pkg ∧ PkgSig bundle completionB pkg ∧
                      hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier terminalRoute completionRouteA completionRouteB completionPkgA completionPkgB
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      hUnary, cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, sameHN⟩
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed hUnary cUnary terminalRoute
  have completionUnaryA : UnaryHistory completionA :=
    unary_cont_closed terminalUnary cUnary completionRouteA
  have completionUnaryB : UnaryHistory completionB :=
    unary_cont_closed terminalUnary cUnary completionRouteB
  have sameCompletion : hsame completionA completionB :=
    cont_deterministic completionRouteA completionRouteB
  exact
    ⟨sameCompletion, terminalUnary, completionUnaryA, completionUnaryB, completionPkgA,
      completionPkgB, sameHN⟩

end BEDC.Derived.CauchyModulusRefinementUp
