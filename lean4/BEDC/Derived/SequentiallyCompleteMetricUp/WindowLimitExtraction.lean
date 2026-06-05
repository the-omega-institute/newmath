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

theorem SequentiallyCompleteMetricWindowLimitExtraction [AskSetup] [PackageSetup]
    {X S R M L D H C P N sourceRead rationalRead modulusRead limitRead distanceRead
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
                      Cont X S sourceRead ->
                        Cont sourceRead R rationalRead ->
                          Cont rationalRead M modulusRead ->
                            Cont modulusRead L limitRead ->
                              Cont limitRead D distanceRead ->
                                Cont distanceRead C replayRead ->
                                  Cont replayRead N completionRead ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle N pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              (hsame row limitRead ∨
                                                hsame row completionRead) ∧
                                                UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row X ∨ hsame row S ∨ hsame row R ∨
                                                hsame row M ∨ hsame row L ∨
                                                  hsame row limitRead ∨ hsame row D ∨
                                                    hsame row completionRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont X S sourceRead ∧
                                                Cont sourceRead R rationalRead ∧
                                                  Cont rationalRead M modulusRead ∧
                                                    Cont modulusRead L limitRead ∧
                                                      Cont limitRead D distanceRead ∧
                                                        Cont distanceRead C replayRead ∧
                                                          Cont replayRead N completionRead ∧
                                                            PkgSig bundle P pkg ∧
                                                              PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory limitRead ∧
                                            UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary rUnary mUnary lUnary dUnary cUnary nUnary sourceRoute
    rationalRoute modulusRoute limitRoute distanceRoute replayRoute completionRoute
    provenancePkg namePkg
  cases fieldRows
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary sUnary sourceRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed sourceUnary rUnary rationalRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed rationalUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed limitUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed replayUnary nUnary completionRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro limitRead ⟨Or.inl (hsame_refl limitRead), limitUnary⟩
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
            | inl sameLimit =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameLimit)
            | inr sameCompletion =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameCompletion)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameLimit =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameLimit)))))
        | inr sameCompletion =>
            exact
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameCompletion))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, sourceRoute, rationalRoute, modulusRoute, limitRoute,
            distanceRoute, replayRoute, completionRoute, provenancePkg, namePkg⟩
    }
  · exact ⟨limitUnary, completionUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
