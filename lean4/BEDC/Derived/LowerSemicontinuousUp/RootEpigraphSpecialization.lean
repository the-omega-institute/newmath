import BEDC.Derived.LowerSemicontinuousUp.RealHandoff
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootEpigraphSpecialization [AskSetup] [PackageSetup]
    {X F E W R O H C P N thresholdRead valueRead epigraphRead comparisonRead
      transportedRead replayRead namedRead : BHist}
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
                    Cont W R valueRead →
                      Cont valueRead E epigraphRead →
                        Cont epigraphRead O comparisonRead →
                          Cont comparisonRead H transportedRead →
                            Cont transportedRead C replayRead →
                              Cont replayRead N namedRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row W ∨ hsame row R ∨ hsame row E ∨
                                            hsame row O ∨ hsame row H ∨ hsame row C ∨
                                              hsame row N ∨ hsame row thresholdRead ∨
                                                hsame row namedRead ∨
                                                  Cont W R valueRead ∨
                                                    Cont valueRead E epigraphRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont W R valueRead ∧
                                            Cont valueRead E epigraphRead ∧
                                              Cont epigraphRead O comparisonRead ∧
                                                Cont comparisonRead H transportedRead ∧
                                                  Cont transportedRead C replayRead ∧
                                                    Cont replayRead N namedRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows wUnary rUnary eUnary oUnary hUnary cUnary nUnary valueRoute
    epigraphRoute comparisonRoute transportedRoute replayRoute namedRoute provenancePkg namePkg
  cases fieldRows
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed wUnary rUnary valueRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed valueUnary eUnary epigraphRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed epigraphUnary oUnary comparisonRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed comparisonUnary hUnary transportedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  constructor
  · exact {
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
                          (Or.inl source.left))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, valueRoute, epigraphRoute, comparisonRoute, transportedRoute,
            replayRoute, namedRoute, provenancePkg, namePkg⟩
    }
  · exact namedUnary

end BEDC.Derived.LowerSemicontinuousUp
