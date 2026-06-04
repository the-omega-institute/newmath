import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousEpigraphLocatedSetExactness [AskSetup] [PackageSetup]
    {X F E W R O H C P N scheduleRead readbackRead epigraphRead locatedRead transportRead
      replayRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory O ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory N ->
                    Cont X W scheduleRead ->
                      Cont scheduleRead R readbackRead ->
                        Cont readbackRead E epigraphRead ->
                          Cont epigraphRead O locatedRead ->
                            Cont locatedRead H transportRead ->
                              Cont transportRead C replayRead ->
                                Cont replayRead N handoffRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row handoffRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row F ∨ hsame row W ∨
                                              hsame row R ∨ hsame row E ∨ hsame row O ∨
                                                hsame row H ∨ hsame row C ∨
                                                  hsame row P ∨ hsame row N ∨
                                                    hsame row handoffRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont X W scheduleRead ∧
                                              Cont scheduleRead R readbackRead ∧
                                                Cont readbackRead E epigraphRead ∧
                                                  Cont epigraphRead O locatedRead ∧
                                                    Cont locatedRead H transportRead ∧
                                                      Cont transportRead C replayRead ∧
                                                        Cont replayRead N handoffRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory scheduleRead ∧
                                          UnaryHistory readbackRead ∧
                                            UnaryHistory epigraphRead ∧
                                              UnaryHistory locatedRead ∧
                                                UnaryHistory transportRead ∧
                                                  UnaryHistory replayRead ∧
                                                    UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro epigraphFields xUnary wUnary rUnary eUnary oUnary hUnary cUnary nUnary scheduleRoute
    readbackRoute epigraphRoute locatedRoute transportRoute replayRoute handoffRoute
    provenancePkg namePkg
  have _acceptedEpigraphFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := epigraphFields
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed xUnary wUnary scheduleRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary rUnary readbackRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed readbackUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed replayUnary nUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W scheduleRead ∧
              Cont scheduleRead R readbackRead ∧ Cont readbackRead E epigraphRead ∧
                Cont epigraphRead O locatedRead ∧ Cont locatedRead H transportRead ∧
                  Cont transportRead C replayRead ∧ Cont replayRead N handoffRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, readbackRoute, epigraphRoute, locatedRoute,
          transportRoute, replayRoute, handoffRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, scheduleUnary, readbackUnary, epigraphUnary, locatedUnary, transportUnary,
      replayUnary, handoffUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
