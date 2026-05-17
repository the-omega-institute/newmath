import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_four_face_pullback_lock
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal streamFace dyadicFace regularFace realFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont W D streamFace ->
          Cont streamFace R dyadicFace ->
            Cont dyadicFace E regularFace ->
              Cont regularFace terminal realFace ->
                PkgSig bundle realFace pkg ->
                  UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
                    UnaryHistory terminal ∧ UnaryHistory streamFace ∧
                      UnaryHistory dyadicFace ∧ UnaryHistory regularFace ∧
                        UnaryHistory realFace ∧ Cont W D streamFace ∧
                          Cont streamFace R dyadicFace ∧
                            Cont dyadicFace E regularFace ∧
                              Cont regularFace terminal realFace ∧ hsame C terminal ∧
                                PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier terminalRoute streamRoute dyadicRoute regularRoute realRoute realPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetSchedule, windowDyadic,
    carrierTerminal, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetSchedule
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowDyadic
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryStreamFace : UnaryHistory streamFace :=
    unary_cont_closed unaryW unaryD streamRoute
  have unaryDyadicFace : UnaryHistory dyadicFace :=
    unary_cont_closed unaryStreamFace unaryR dyadicRoute
  have unaryRegularFace : UnaryHistory regularFace :=
    unary_cont_closed unaryDyadicFace unaryE regularRoute
  have unaryRealFace : UnaryHistory realFace :=
    unary_cont_closed unaryRegularFace unaryTerminal realRoute
  have sameTerminal : hsame C terminal :=
    cont_deterministic carrierTerminal terminalRoute
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unaryTerminal, unaryStreamFace, unaryDyadicFace,
      unaryRegularFace, unaryRealFace, streamRoute, dyadicRoute, regularRoute, realRoute,
      sameTerminal, realPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
