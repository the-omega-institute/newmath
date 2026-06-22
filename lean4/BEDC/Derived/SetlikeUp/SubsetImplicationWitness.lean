import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SetlikeSubsetImplicationWitness [AskSetup] [PackageSetup] (S : SetlikeUp)
    {M Q I R E H C P N classifierRead subsetWitness transportedWitness replayWitness
      namedWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] →
      UnaryHistory M →
        UnaryHistory Q →
          UnaryHistory I →
            UnaryHistory H →
              UnaryHistory C →
                UnaryHistory N →
                  Cont M Q classifierRead →
                    Cont classifierRead I subsetWitness →
                      Cont subsetWitness H transportedWitness →
                        Cont transportedWitness C replayWitness →
                          Cont replayWitness N namedWitness →
                            PkgSig bundle P pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row namedWitness ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row Q ∨ hsame row I ∨
                                      hsame row H ∨ hsame row C ∨ hsame row N ∨
                                        hsame row classifierRead ∨
                                          hsame row subsetWitness ∨
                                            hsame row transportedWitness ∨
                                              hsame row replayWitness ∨
                                                hsame row namedWitness)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M Q classifierRead ∧
                                      Cont classifierRead I subsetWitness ∧
                                        Cont subsetWitness H transportedWitness ∧
                                          Cont transportedWitness C replayWitness ∧
                                            Cont replayWitness N namedWitness ∧
                                              PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory subsetWitness ∧ UnaryHistory namedWitness := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro _fields mUnary qUnary iUnary hUnary cUnary nUnary classifierRoute subsetRoute
    transportRoute replayRoute nameRoute provenancePkg
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed mUnary qUnary classifierRoute
  have subsetUnary : UnaryHistory subsetWitness :=
    unary_cont_closed classifierUnary iUnary subsetRoute
  have transportedUnary : UnaryHistory transportedWitness :=
    unary_cont_closed subsetUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayWitness :=
    unary_cont_closed transportedUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedWitness :=
    unary_cont_closed replayUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedWitness ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row H ∨ hsame row C ∨
              hsame row N ∨ hsame row classifierRead ∨ hsame row subsetWitness ∨
                hsame row transportedWitness ∨ hsame row replayWitness ∨
                  hsame row namedWitness)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q classifierRead ∧
              Cont classifierRead I subsetWitness ∧ Cont subsetWitness H transportedWitness ∧
                Cont transportedWitness C replayWitness ∧ Cont replayWitness N namedWitness ∧
                  PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedWitness ⟨hsame_refl namedWitness, namedUnary⟩
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
                          (Or.inr (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, classifierRoute, subsetRoute, transportRoute, replayRoute,
            nameRoute, provenancePkg⟩
    }
  exact ⟨cert, subsetUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
