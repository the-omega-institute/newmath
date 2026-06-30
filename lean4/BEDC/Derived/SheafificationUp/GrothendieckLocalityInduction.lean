import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationGrothendieckLocalityInduction [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N : BHist} :
    UnaryHistory C →
      UnaryHistory T →
        UnaryHistory P →
          UnaryHistory G →
            UnaryHistory H →
              UnaryHistory Q →
                Cont C T J →
                  Cont J P L →
                    Cont L G S →
                      Cont S H R →
                        Cont R Q N →
                          forall refinements : List BHist,
                            (forall r : BHist, r ∈ refinements -> UnaryHistory r) ->
                              exists route : BHist,
                                UnaryHistory route ∧ hsame route (refinements.foldl append N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro cUnary tUnary pUnary gUnary hUnary qUnary siteRoute localityRoute gluingRoute
    transportRoute replayRoute refinements refinementsUnary
  have jUnary : UnaryHistory J :=
    unary_cont_closed cUnary tUnary siteRoute
  have lUnary : UnaryHistory L :=
    unary_cont_closed jUnary pUnary localityRoute
  have sUnary : UnaryHistory S :=
    unary_cont_closed lUnary gUnary gluingRoute
  have rUnary : UnaryHistory R :=
    unary_cont_closed sUnary hUnary transportRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed rUnary qUnary replayRoute
  have foldUnaryFrom :
      forall (acc : BHist) (rows : List BHist),
        UnaryHistory acc →
          (forall row : BHist, row ∈ rows -> UnaryHistory row) →
            UnaryHistory (rows.foldl append acc) := by
    intro acc rows accUnary rowsUnary
    induction rows generalizing acc with
    | nil =>
        exact accUnary
    | cons row rest ih =>
        have rowUnary : UnaryHistory row :=
          rowsUnary row (List.Mem.head rest)
        have restUnary : forall tail : BHist, tail ∈ rest -> UnaryHistory tail := by
          intro tail tailMem
          exact rowsUnary tail (List.Mem.tail row tailMem)
        exact ih (append acc row) (unary_append_closed accUnary rowUnary) restUnary
  exact Exists.intro (refinements.foldl append N)
    ⟨foldUnaryFrom N refinements nUnary refinementsUnary,
      hsame_refl (refinements.foldl append N)⟩

end BEDC.Derived.SheafificationUp
