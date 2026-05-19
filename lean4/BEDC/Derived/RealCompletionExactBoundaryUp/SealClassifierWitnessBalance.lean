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

theorem RealCompletionExactBoundarySealClassifierWitnessBalance [AskSetup] [PackageSetup]
    {limitSeal classifier witness synchronizer window readback dyadic terminal sealClassifier
      witnessBudget streamReg terminalRead balanceRead : BHist}
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
                        Cont sealClassifier witnessBudget balanceRead →
                          Cont window readback streamReg →
                            Cont dyadic terminal terminalRead →
                              PkgSig bundle balanceRead pkg →
                                UnaryHistory sealClassifier ∧
                                  UnaryHistory witnessBudget ∧
                                    UnaryHistory balanceRead ∧
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row balanceRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row sealClassifier ∨
                                            hsame row witnessBudget ∨
                                              hsame row balanceRead)
                                        (fun row : BHist =>
                                          hsame row balanceRead ∧
                                            PkgSig bundle balanceRead pkg)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro limitSealUnary classifierUnary witnessUnary synchronizerUnary _windowUnary
    _readbackUnary _dyadicUnary _terminalUnary sealRoute witnessRoute balanceRoute
    _streamRoute _terminalRoute balancePkg
  have sealClassifierUnary : UnaryHistory sealClassifier :=
    unary_cont_closed limitSealUnary classifierUnary sealRoute
  have witnessBudgetUnary : UnaryHistory witnessBudget :=
    unary_cont_closed witnessUnary synchronizerUnary witnessRoute
  have balanceReadUnary : UnaryHistory balanceRead :=
    unary_cont_closed sealClassifierUnary witnessBudgetUnary balanceRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row balanceRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row sealClassifier ∨ hsame row witnessBudget ∨ hsame row balanceRead)
        (fun row : BHist => hsame row balanceRead ∧ PkgSig bundle balanceRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro balanceRead ⟨hsame_refl balanceRead, balanceReadUnary⟩
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
        exact ⟨source.left, balancePkg⟩
    }
  exact ⟨sealClassifierUnary, witnessBudgetUnary, balanceReadUnary, cert⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
