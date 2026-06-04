import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousFiniteEpigraphThresholdExhaustion [AskSetup] [PackageSetup]
    {X F E W R O H C P N windowRead epigraphRead locatedRead transportRead replayRead
      thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont W R windowRead ->
                      Cont windowRead E epigraphRead ->
                        Cont epigraphRead O locatedRead ->
                          Cont locatedRead H transportRead ->
                            Cont transportRead C replayRead ->
                              Cont replayRead N thresholdRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle N pkg ->
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row thresholdRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row X ∨ hsame row F ∨ hsame row W ∨
                                          hsame row R ∨ hsame row E ∨ hsame row O ∨
                                            hsame row H ∨ hsame row C ∨ hsame row P ∨
                                              hsame row N ∨ hsame row thresholdRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont W R windowRead ∧
                                          Cont windowRead E epigraphRead ∧
                                            Cont epigraphRead O locatedRead ∧
                                              Cont locatedRead H transportRead ∧
                                                Cont transportRead C replayRead ∧
                                                  Cont replayRead N thresholdRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                      hsame ∧
                                      UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                                        UnaryHistory locatedRead ∧
                                          UnaryHistory transportRead ∧
                                            UnaryHistory replayRead ∧
                                              UnaryHistory thresholdRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro epigraphFields wUnary rUnary eUnary oUnary hUnary cUnary nUnary windowRoute
    epigraphRoute locatedRoute transportRoute replayRoute thresholdRoute provenancePkg namePkg
  have _acceptedEpigraphFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := epigraphFields
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary eUnary epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed replayUnary nUnary thresholdRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row thresholdRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row O ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row thresholdRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead E epigraphRead ∧
              Cont epigraphRead O locatedRead ∧ Cont locatedRead H transportRead ∧
                Cont transportRead C replayRead ∧ Cont replayRead N thresholdRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro thresholdRead ⟨hsame_refl thresholdRead, thresholdUnary⟩
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
        ⟨source.right, windowRoute, epigraphRoute, locatedRoute, transportRoute,
          replayRoute, thresholdRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, windowUnary, epigraphUnary, locatedUnary, transportUnary, replayUnary,
      thresholdUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
