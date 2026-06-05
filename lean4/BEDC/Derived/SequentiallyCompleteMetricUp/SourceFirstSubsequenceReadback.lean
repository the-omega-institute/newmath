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

theorem SequentiallyCompleteMetricSourceFirstSubsequenceReadback [AskSetup] [PackageSetup]
    {X S M L D H C P N subsequenceRead completionRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory S →
          UnaryHistory M →
            UnaryHistory L →
              UnaryHistory D →
                UnaryHistory C →
                  Cont X S subsequenceRead →
                    Cont subsequenceRead L completionRead →
                      Cont completionRead C replayRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row S ∨ hsame row L ∨
                                    hsame row D ∨ hsame row replayRead ∨
                                      Cont completionRead C replayRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont X S subsequenceRead ∧
                                    Cont subsequenceRead L completionRead ∧
                                      Cont completionRead C replayRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory subsequenceRead ∧ UnaryHistory completionRead ∧
                                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary _mUnary lUnary _dUnary cUnary subsequenceRoute
    completionRoute replayRoute provenancePkg namePkg
  cases fieldRows
  have subsequenceUnary : UnaryHistory subsequenceRead :=
    unary_cont_closed xUnary sUnary subsequenceRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed subsequenceUnary lUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row L ∨ hsame row D ∨
              hsame row replayRead ∨ Cont completionRead C replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X S subsequenceRead ∧
              Cont subsequenceRead L completionRead ∧ Cont completionRead C replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, subsequenceRoute, completionRoute, replayRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, subsequenceUnary, completionUnary, replayUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
