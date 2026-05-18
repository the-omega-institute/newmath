import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryFourFaceExactness [AskSetup] [PackageSetup]
    {limitSeal classifier witness synchronizer window readback dyadic terminal _transport _replay
      _provenance _name sealClassifier witnessBudget streamReg terminalRead fourFaceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory limitSeal →
      UnaryHistory classifier →
        UnaryHistory witness →
          UnaryHistory synchronizer →
            UnaryHistory window →
              UnaryHistory readback →
                UnaryHistory dyadic →
                  UnaryHistory terminal →
                    Cont limitSeal classifier sealClassifier →
                      Cont witness synchronizer witnessBudget →
                        Cont window readback streamReg →
                          Cont dyadic terminal terminalRead →
                            Cont streamReg terminalRead fourFaceRead →
                              PkgSig bundle fourFaceRead pkg →
                                UnaryHistory sealClassifier ∧ UnaryHistory witnessBudget ∧
                                  UnaryHistory streamReg ∧ UnaryHistory terminalRead ∧
                                    UnaryHistory fourFaceRead ∧
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row fourFaceRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row streamReg ∨
                                            hsame row terminalRead ∨
                                              hsame row fourFaceRead)
                                        (fun row : BHist =>
                                          PkgSig bundle fourFaceRead pkg ∧
                                            hsame row fourFaceRead)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro limitSealUnary classifierUnary witnessUnary synchronizerUnary windowUnary
    readbackUnary dyadicUnary terminalUnary sealRoute witnessRoute streamRoute
    terminalRoute fourFaceRoute fourFacePkg
  have sealClassifierUnary : UnaryHistory sealClassifier :=
    unary_cont_closed limitSealUnary classifierUnary sealRoute
  have witnessBudgetUnary : UnaryHistory witnessBudget :=
    unary_cont_closed witnessUnary synchronizerUnary witnessRoute
  have streamRegUnary : UnaryHistory streamReg :=
    unary_cont_closed windowUnary readbackUnary streamRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed dyadicUnary terminalUnary terminalRoute
  have fourFaceReadUnary : UnaryHistory fourFaceRead :=
    unary_cont_closed streamRegUnary terminalReadUnary fourFaceRoute
  have sourceFourFace :
      (fun row : BHist => hsame row fourFaceRead ∧ UnaryHistory row) fourFaceRead := by
    exact ⟨hsame_refl fourFaceRead, fourFaceReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row fourFaceRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row streamReg ∨ hsame row terminalRead ∨ hsame row fourFaceRead)
        (fun row : BHist => PkgSig bundle fourFaceRead pkg ∧ hsame row fourFaceRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro fourFaceRead sourceFourFace
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨fourFacePkg, source.left⟩
    }
  exact
    ⟨sealClassifierUnary, witnessBudgetUnary, streamRegUnary, terminalReadUnary,
      fourFaceReadUnary, cert⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
