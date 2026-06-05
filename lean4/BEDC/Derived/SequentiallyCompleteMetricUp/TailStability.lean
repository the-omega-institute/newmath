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

theorem SequentiallyCompleteMetricTailStability [AskSetup] [PackageSetup]
    {X S M L D H C P N tailRead tailReadPrime boundRead boundReadPrime replayRead
      replayReadPrime handoffRead handoffReadPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory D ->
              UnaryHistory C ->
                UnaryHistory N ->
                  Cont X S tailRead ->
                    Cont X S tailReadPrime ->
                      Cont tailRead M boundRead ->
                        Cont tailReadPrime M boundReadPrime ->
                          Cont boundRead D replayRead ->
                            Cont boundReadPrime D replayReadPrime ->
                              Cont replayRead N handoffRead ->
                                Cont replayReadPrime N handoffReadPrime ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row handoffRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row S ∨ hsame row M ∨
                                              hsame row D ∨ hsame row handoffRead ∨
                                                hsame row handoffReadPrime)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont X S tailRead ∧
                                              Cont X S tailReadPrime ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory handoffRead ∧
                                          UnaryHistory handoffReadPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary mUnary dUnary _cUnary nUnary tailRoute tailRoutePrime
    boundRoute boundRoutePrime replayRoute replayRoutePrime handoffRoute handoffRoutePrime
    provenancePkg namePkg
  cases fieldRows
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed xUnary sUnary tailRoute
  have tailPrimeUnary : UnaryHistory tailReadPrime :=
    unary_cont_closed xUnary sUnary tailRoutePrime
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed tailUnary mUnary boundRoute
  have boundPrimeUnary : UnaryHistory boundReadPrime :=
    unary_cont_closed tailPrimeUnary mUnary boundRoutePrime
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed boundUnary dUnary replayRoute
  have replayPrimeUnary : UnaryHistory replayReadPrime :=
    unary_cont_closed boundPrimeUnary dUnary replayRoutePrime
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed replayUnary nUnary handoffRoute
  have handoffPrimeUnary : UnaryHistory handoffReadPrime :=
    unary_cont_closed replayPrimeUnary nUnary handoffRoutePrime
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro handoffRead (And.intro (hsame_refl handoffRead) handoffUnary)
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
          intro _row _other sameRows sourceRow
          exact
            And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
              (unary_transport sourceRow.right sameRows)
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact
          And.intro sourceRow.right
            (And.intro tailRoute
              (And.intro tailRoutePrime (And.intro provenancePkg namePkg)))
    }
  · exact And.intro handoffUnary handoffPrimeUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
