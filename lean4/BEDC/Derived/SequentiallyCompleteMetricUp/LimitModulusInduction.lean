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

theorem SequentiallyCompleteMetricLimitModulusInduction [AskSetup] [PackageSetup]
    {X S M L D H C P N request sequenceRead modulusRead limitRead distanceRead
      replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory request ->
        UnaryHistory X ->
          UnaryHistory S ->
            UnaryHistory M ->
              UnaryHistory L ->
                UnaryHistory D ->
                  UnaryHistory C ->
                    UnaryHistory N ->
                      Cont X S sequenceRead ->
                        Cont sequenceRead M modulusRead ->
                          Cont modulusRead L limitRead ->
                            Cont limitRead D distanceRead ->
                              Cont distanceRead C replayRead ->
                                Cont replayRead N namedRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          (hsame row request ∨ hsame row modulusRead ∨
                                            hsame row limitRead ∨ hsame row namedRead) ∧
                                            UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row M ∨ hsame row S ∨ hsame row L ∨
                                            hsame row D ∨ hsame row request ∨
                                              Cont sequenceRead M modulusRead ∨
                                                Cont modulusRead L limitRead ∨
                                                  Cont limitRead D distanceRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont sequenceRead M modulusRead ∧
                                              Cont modulusRead L limitRead ∧
                                                Cont limitRead D distanceRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                        hsame ∧
                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows requestUnary xUnary sUnary mUnary lUnary dUnary cUnary nUnary
    sequenceRoute modulusRoute limitRoute distanceRoute replayRoute namedRoute provenancePkg
    namePkg
  cases fieldRows
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sequenceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro request
            (And.intro (Or.inl (hsame_refl request)) requestUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact And.intro
            (by
              cases source.left with
              | inl sameRequest =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameRequest)
              | inr rest =>
                  cases rest with
                  | inl sameModulus =>
                      exact Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameModulus))
                  | inr rest =>
                      cases rest with
                      | inl sameLimit =>
                          exact Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameLimit)))
                      | inr sameNamed =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) sameNamed))))
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameRequest =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRequest))))
        | inr rest =>
            cases rest with
            | inl _sameModulus =>
                exact Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl modulusRoute)))))
            | inr rest =>
                cases rest with
                | inl _sameLimit =>
                    exact Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inl limitRoute))))))
                | inr _sameNamed =>
                    exact Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr distanceRoute))))))
      ledger_sound := by
        intro _row source
        exact And.intro source.right
          (And.intro modulusRoute
            (And.intro limitRoute
              (And.intro distanceRoute
                (And.intro provenancePkg namePkg))))
    }
  · exact namedUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
