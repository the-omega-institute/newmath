import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousLocatedEpigraphFilterStability [AskSetup] [PackageSetup]
    {X F E W R O H C P N filterRead thresholdRead transported replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] ->
      UnaryHistory W -> UnaryHistory R -> UnaryHistory E -> UnaryHistory O ->
        UnaryHistory H -> UnaryHistory C -> UnaryHistory N ->
          Cont W R filterRead -> Cont filterRead E thresholdRead ->
            Cont thresholdRead H transported -> Cont transported C replayRead ->
              Cont replayRead N namedRead -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
                        hsame row H ∨ hsame row C ∨ hsame row N ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W R filterRead ∧
                        Cont filterRead E thresholdRead ∧ Cont thresholdRead H transported ∧
                          Cont transported C replayRead ∧ Cont replayRead N namedRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory filterRead ∧ UnaryHistory thresholdRead ∧
                    UnaryHistory transported ∧ UnaryHistory replayRead ∧
                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro fields wUnary rUnary eUnary _oUnary hUnary cUnary nUnary filterRoute thresholdRoute
    transportRoute replayRoute namedRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed wUnary rUnary filterRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed filterUnary eUnary thresholdRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed thresholdUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R filterRead ∧ Cont filterRead E thresholdRead ∧
              Cont thresholdRead H transported ∧ Cont transported C replayRead ∧
                Cont replayRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, filterRoute, thresholdRoute, transportRoute, replayRoute, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, filterUnary, thresholdUnary, transportedUnary, replayUnary, namedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
