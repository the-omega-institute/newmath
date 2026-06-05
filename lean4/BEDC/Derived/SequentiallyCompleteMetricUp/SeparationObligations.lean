import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricSeparationObligations [AskSetup] [PackageSetup]
    {X S M L D H C P N windowRead readbackRead lateDistanceRead handoffRead
      transportedRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory S →
          UnaryHistory M →
            UnaryHistory L →
              UnaryHistory D →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory N →
                      Cont X S windowRead →
                        Cont windowRead M readbackRead →
                          Cont readbackRead D lateDistanceRead →
                            Cont lateDistanceRead L handoffRead →
                              Cont handoffRead H transportedRead →
                                Cont transportedRead C replayRead →
                                  Cont replayRead N namedRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row X ∨ hsame row S ∨ hsame row M ∨
                                                hsame row L ∨ hsame row D ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row N ∨
                                                    hsame row namedRead ∨
                                                      Cont handoffRead H transportedRead ∨
                                                        Cont transportedRead C replayRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont X S windowRead ∧
                                                Cont windowRead M readbackRead ∧
                                                  Cont readbackRead D lateDistanceRead ∧
                                                    Cont lateDistanceRead L handoffRead ∧
                                                      Cont handoffRead H transportedRead ∧
                                                        Cont transportedRead C replayRead ∧
                                                          Cont replayRead N namedRead ∧
                                                            PkgSig bundle P pkg ∧
                                                              PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary mUnary lUnary dUnary hUnary cUnary nUnary windowRoute
    readbackRoute lateDistanceRoute handoffRoute transportedRoute replayRoute namedRoute
    provenancePkg namePkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed xUnary sUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary mUnary readbackRoute
  have lateDistanceUnary : UnaryHistory lateDistanceRead :=
    unary_cont_closed readbackUnary dUnary lateDistanceRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed lateDistanceUnary lUnary handoffRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed handoffUnary hUnary transportedRoute
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
          ⟨source.right, windowRoute, readbackRoute, lateDistanceRoute, handoffRoute,
            transportedRoute, replayRoute, namedRoute, provenancePkg, namePkg⟩
    }
  · exact namedUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
