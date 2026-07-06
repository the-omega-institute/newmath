import BEDC.Derived.FiniteWindowRealSeparationUp.ScopedKernelRoute

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWindowRealSeparation_scoped_completion_route [AskSetup] [PackageSetup]
    {x : FiniteWindowRealSeparationUp}
    {W D S R H C P N toleranceRead readbackRead realRead exactBoundaryRead
      budgetSealRead tailMeetRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteWindowRealSeparationToEventFlow x =
        finiteWindowRealSeparationToEventFlow
          (FiniteWindowRealSeparationUp.mk W D S R H C P N) ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont W D toleranceRead ->
                        Cont toleranceRead S readbackRead ->
                          Cont readbackRead R realRead ->
                            Cont realRead H exactBoundaryRead ->
                              Cont exactBoundaryRead C budgetSealRead ->
                                Cont budgetSealRead P tailMeetRead ->
                                  Cont tailMeetRead N completionRead ->
                                    PkgSig bundle completionRead pkg ->
                                      x = FiniteWindowRealSeparationUp.mk W D S R H C P N ∧
                                        UnaryHistory completionRead ∧
                                          SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row completionRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row W ∨ hsame row D ∨ hsame row S ∨
                                                hsame row R ∨ hsame row H ∨ hsame row C ∨
                                                  hsame row P ∨ hsame row N ∨
                                                    hsame row toleranceRead ∨
                                                      hsame row readbackRead ∨
                                                        hsame row realRead ∨
                                                          hsame row exactBoundaryRead ∨
                                                            hsame row budgetSealRead ∨
                                                              hsame row tailMeetRead ∨
                                                                hsame row completionRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont W D toleranceRead ∧
                                                Cont toleranceRead S readbackRead ∧
                                                  Cont readbackRead R realRead ∧
                                                    Cont realRead H exactBoundaryRead ∧
                                                      Cont exactBoundaryRead C budgetSealRead ∧
                                                        Cont budgetSealRead P tailMeetRead ∧
                                                          Cont tailMeetRead N completionRead ∧
                                                            PkgSig bundle completionRead pkg)
                                            hsame := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory ChapterTasteGate
  intro flowEq unaryW unaryD unaryS unaryR unaryH unaryC unaryP unaryN toleranceRoute
    readbackRoute realRoute exactBoundaryRoute budgetSealRoute tailMeetRoute completionRoute
    completionPkg
  have flowInjective :
      ∀ x y : FiniteWindowRealSeparationUp,
        finiteWindowRealSeparationToEventFlow x =
          finiteWindowRealSeparationToEventFlow y → x = y :=
    FiniteWindowRealSeparationTasteGate_single_carrier_alignment.right.right.left
  have carrierEq : x = FiniteWindowRealSeparationUp.mk W D S R H C P N :=
    flowInjective x (FiniteWindowRealSeparationUp.mk W D S R H C P N) flowEq
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryS readbackRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary unaryR realRoute
  have exactBoundaryUnary : UnaryHistory exactBoundaryRead :=
    unary_cont_closed realUnary unaryH exactBoundaryRoute
  have budgetSealUnary : UnaryHistory budgetSealRead :=
    unary_cont_closed exactBoundaryUnary unaryC budgetSealRoute
  have tailMeetUnary : UnaryHistory tailMeetRead :=
    unary_cont_closed budgetSealUnary unaryP tailMeetRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed tailMeetUnary unaryN completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row toleranceRead ∨
                hsame row readbackRead ∨ hsame row realRead ∨
                  hsame row exactBoundaryRead ∨ hsame row budgetSealRead ∨
                    hsame row tailMeetRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead ∧ Cont readbackRead R realRead ∧
                Cont realRead H exactBoundaryRead ∧
                  Cont exactBoundaryRead C budgetSealRead ∧
                    Cont budgetSealRead P tailMeetRead ∧
                      Cont tailMeetRead N completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceRoute, readbackRoute, realRoute, exactBoundaryRoute,
        budgetSealRoute, tailMeetRoute, completionRoute, completionPkg⟩
  }
  exact ⟨carrierEq, completionUnary, cert⟩

end BEDC.Derived.FiniteWindowRealSeparationUp
