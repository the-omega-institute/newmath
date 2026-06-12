import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootLocatedSetNonescape [AskSetup] [PackageSetup]
    {X F E W R O H C P N scheduleRead readbackRead epigraphRead locatedRead transportRead
      replayRead handoffRead bypassRead : BHist}
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
                                    Cont locatedRead handoffRead bypassRead ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle N pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                (hsame row handoffRead ∨ hsame row bypassRead) ∧
                                                  UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row W ∨ hsame row R ∨ hsame row E ∨
                                                  hsame row O ∨ hsame row H ∨ hsame row C ∨
                                                    hsame row N ∨ hsame row handoffRead ∨
                                                      hsame row bypassRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont X W scheduleRead ∧
                                                  Cont scheduleRead R readbackRead ∧
                                                    Cont readbackRead E epigraphRead ∧
                                                      Cont epigraphRead O locatedRead ∧
                                                        Cont locatedRead H transportRead ∧
                                                          Cont transportRead C replayRead ∧
                                                            Cont replayRead N handoffRead ∧
                                                              Cont locatedRead handoffRead bypassRead ∧
                                                                PkgSig bundle P pkg ∧
                                                                  PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory handoffRead ∧ UnaryHistory bypassRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro epigraphFields xUnary wUnary rUnary eUnary oUnary hUnary cUnary nUnary scheduleRoute
    readbackRoute epigraphRoute locatedRoute transportRoute replayRoute handoffRoute bypassRoute
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
  have bypassUnary : UnaryHistory bypassRead :=
    unary_cont_closed locatedUnary handoffUnary bypassRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row handoffRead ∨ hsame row bypassRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row N ∨ hsame row handoffRead ∨ hsame row bypassRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W scheduleRead ∧ Cont scheduleRead R readbackRead ∧
              Cont readbackRead E epigraphRead ∧ Cont epigraphRead O locatedRead ∧
                Cont locatedRead H transportRead ∧ Cont transportRead C replayRead ∧
                  Cont replayRead N handoffRead ∧ Cont locatedRead handoffRead bypassRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bypassRead ⟨Or.inr (hsame_refl bypassRead), bypassUnary⟩
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
        constructor
        · cases source.left with
          | inl sameHandoff =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameHandoff)
          | inr sameBypass =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameBypass)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameHandoff =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl sameHandoff)))))))
      | inr sameBypass =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr sameBypass)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, readbackRoute, epigraphRoute, locatedRoute,
          transportRoute, replayRoute, handoffRoute, bypassRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, handoffUnary, bypassUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
