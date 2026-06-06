import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRealRegSeqRatScope [AskSetup] [PackageSetup]
    {X F E W R O H C P N scheduleRead epigraphRead comparisonRead transportRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory O →
              UnaryHistory H →
                UnaryHistory N →
                  Cont W R scheduleRead →
                    Cont scheduleRead E epigraphRead →
                      Cont epigraphRead O comparisonRead →
                        Cont comparisonRead H transportRead →
                          Cont transportRead N namedRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row W ∨ hsame row R ∨ hsame row E ∨
                                        hsame row O ∨ hsame row H ∨ hsame row N ∨
                                          hsame row scheduleRead ∨ hsame row epigraphRead ∨
                                            hsame row comparisonRead ∨
                                              hsame row transportRead ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont W R scheduleRead ∧
                                        Cont scheduleRead E epigraphRead ∧
                                          Cont epigraphRead O comparisonRead ∧
                                            Cont comparisonRead H transportRead ∧
                                              Cont transportRead N namedRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧ UnaryHistory scheduleRead ∧
                                  UnaryHistory epigraphRead ∧ UnaryHistory comparisonRead ∧
                                    UnaryHistory transportRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary hUnary nUnary scheduleRoute epigraphRoute
    comparisonRoute transportRoute namedRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed wUnary rUnary scheduleRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed scheduleUnary eUnary epigraphRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed epigraphUnary oUnary comparisonRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed comparisonUnary hUnary transportRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed transportUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
              hsame row N ∨ hsame row scheduleRead ∨ hsame row epigraphRead ∨
                hsame row comparisonRead ∨ hsame row transportRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R scheduleRead ∧ Cont scheduleRead E epigraphRead ∧
              Cont epigraphRead O comparisonRead ∧ Cont comparisonRead H transportRead ∧
                Cont transportRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        ⟨source.right, scheduleRoute, epigraphRoute, comparisonRoute, transportRoute,
          namedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, scheduleUnary, epigraphUnary, comparisonUnary, transportUnary, namedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
