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

theorem SequentiallyCompleteMetricLimitReadbackPackage [AskSetup] [PackageSetup]
    {X S R M L D H C P N sequenceRead regularRead modulusRead limitRead distanceRead
      replayRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory R ->
            UnaryHistory M ->
              UnaryHistory L ->
                UnaryHistory D ->
                  UnaryHistory C ->
                    UnaryHistory N ->
                      Cont X S sequenceRead ->
                        Cont sequenceRead R regularRead ->
                          Cont regularRead M modulusRead ->
                            Cont modulusRead L limitRead ->
                              Cont limitRead D distanceRead ->
                                Cont distanceRead C replayRead ->
                                  Cont replayRead N completionRead ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row limitRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row X ∨ hsame row S ∨ hsame row R ∨
                                                hsame row M ∨ hsame row L ∨ hsame row D ∨
                                                  Cont replayRead N completionRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont X S sequenceRead ∧
                                                Cont sequenceRead R regularRead ∧
                                                  Cont regularRead M modulusRead ∧
                                                    Cont modulusRead L limitRead ∧
                                                      Cont limitRead D distanceRead ∧
                                                        Cont distanceRead C replayRead ∧
                                                          Cont replayRead N completionRead ∧
                                                            PkgSig bundle P pkg ∧
                                                              PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary rUnary mUnary lUnary dUnary cUnary nUnary sequenceRoute
    regularRoute modulusRoute limitRoute distanceRoute replayRoute completionRoute provenancePkg
    namePkg
  cases fieldRows
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sequenceUnary rUnary regularRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed regularUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro limitRead (And.intro (hsame_refl limitRead) limitUnary)
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
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr completionRoute)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, sequenceRoute, regularRoute, modulusRoute, limitRoute,
            distanceRoute, replayRoute, completionRoute, provenancePkg, namePkg⟩
    }
  · exact limitUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
