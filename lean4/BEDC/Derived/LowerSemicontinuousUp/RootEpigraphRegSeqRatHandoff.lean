import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphRegSeqRatHandoff [AskSetup] [PackageSetup]
    {X F E W R O H C P N scheduleRead readbackRead epigraphRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory C ->
                Cont X W scheduleRead ->
                  Cont scheduleRead R readbackRead ->
                    Cont readbackRead E epigraphRead ->
                      Cont epigraphRead C handoffRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                    hsame row scheduleRead ∨ hsame row readbackRead ∨
                                      hsame row epigraphRead ∨ hsame row handoffRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont X W scheduleRead ∧
                                  Cont scheduleRead R readbackRead ∧
                                    Cont readbackRead E epigraphRead ∧
                                      Cont epigraphRead C handoffRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧ UnaryHistory scheduleRead ∧
                                UnaryHistory readbackRead ∧ UnaryHistory epigraphRead ∧
                                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig SemanticNameCert UnaryHistory
  intro fields xUnary wUnary rUnary eUnary cUnary scheduleRoute readbackRoute epigraphRoute
    handoffRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed xUnary wUnary scheduleRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary rUnary readbackRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed readbackUnary eUnary epigraphRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed epigraphUnary cUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row scheduleRead ∨
                hsame row readbackRead ∨ hsame row epigraphRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W scheduleRead ∧ Cont scheduleRead R readbackRead ∧
              Cont readbackRead E epigraphRead ∧ Cont epigraphRead C handoffRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, readbackRoute, epigraphRoute, handoffRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, epigraphUnary, handoffUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
