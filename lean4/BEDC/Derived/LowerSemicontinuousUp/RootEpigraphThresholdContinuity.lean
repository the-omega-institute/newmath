import BEDC.Derived.LowerSemicontinuousUp.RootEpigraphFilterBasisExactness
import BEDC.FKernel.Cont

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphThresholdContinuity [AskSetup] [PackageSetup]
    {X F E W R O H C P N filterRead thresholdRead locatedRead transportRead replayRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory O →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont W R filterRead →
                      Cont filterRead E thresholdRead →
                        Cont thresholdRead O locatedRead →
                          Cont locatedRead H transportRead →
                            Cont transportRead C replayRead →
                              Cont replayRead N namedRead →
                                hsame H (append C P) →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row W ∨ hsame row R ∨
                                              hsame row E ∨ hsame row O ∨
                                                hsame row H ∨ hsame row C ∨
                                                  hsame row P ∨ hsame row N ∨
                                                    hsame row filterRead ∨
                                                      hsame row thresholdRead ∨
                                                        hsame row locatedRead ∨
                                                          hsame row transportRead ∨
                                                            hsame row replayRead ∨
                                                              hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont W R filterRead ∧
                                              Cont filterRead E thresholdRead ∧
                                                Cont thresholdRead O locatedRead ∧
                                                  Cont locatedRead H transportRead ∧
                                                    Cont transportRead C replayRead ∧
                                                      Cont replayRead N namedRead ∧
                                                        hsame H (append C P) ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory filterRead ∧
                                          UnaryHistory thresholdRead ∧
                                            UnaryHistory locatedRead ∧
                                              UnaryHistory transportRead ∧
                                                UnaryHistory replayRead ∧
                                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields wUnary rUnary eUnary oUnary hUnary cUnary nUnary filterRoute thresholdRoute
    locatedRoute transportRoute replayRoute namedRoute transportSame provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootEpigraphFields
          (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] := fields
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed wUnary rUnary filterRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed filterUnary eUnary thresholdRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed thresholdUnary oUnary locatedRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed locatedUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row filterRead ∨
                hsame row thresholdRead ∨ hsame row locatedRead ∨ hsame row transportRead ∨
                  hsame row replayRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R filterRead ∧ Cont filterRead E thresholdRead ∧
              Cont thresholdRead O locatedRead ∧ Cont locatedRead H transportRead ∧
                Cont transportRead C replayRead ∧ Cont replayRead N namedRead ∧
                  hsame H (append C P) ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, filterRoute, thresholdRoute, locatedRoute, transportRoute,
          replayRoute, namedRoute, transportSame, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, filterUnary, thresholdUnary, locatedUnary, transportUnary, replayUnary,
      namedUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
