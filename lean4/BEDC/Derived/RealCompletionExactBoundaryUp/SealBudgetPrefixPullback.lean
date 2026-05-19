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

theorem RealCompletionExactBoundarySealBudgetPrefixPullback [AskSetup] [PackageSetup]
    {limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
      provenance name sealClassifier witnessBudget streamReg terminalRead prefixRead
      prefixStreamRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory limitSeal ->
      UnaryHistory classifier ->
        UnaryHistory witness ->
          UnaryHistory synchronizer ->
            UnaryHistory window ->
              UnaryHistory readback ->
                UnaryHistory dyadic ->
                  UnaryHistory terminal ->
                    Cont limitSeal classifier sealClassifier ->
                      Cont witness synchronizer witnessBudget ->
                        Cont window readback streamReg ->
                          Cont dyadic terminal terminalRead ->
                            Cont sealClassifier witnessBudget prefixRead ->
                              Cont prefixRead streamReg prefixStreamRead ->
                                Cont prefixStreamRead terminalRead consumer ->
                                  PkgSig bundle consumer pkg ->
                                    realCompletionExactBoundaryFields
                                        (RealCompletionExactBoundaryUp.mk limitSeal classifier
                                          witness synchronizer window readback dyadic terminal
                                          transport replay provenance name) =
                                      [limitSeal, classifier, witness, synchronizer, window,
                                        readback, dyadic, terminal, transport, replay,
                                        provenance, name] ∧
                                      UnaryHistory prefixRead ∧
                                        UnaryHistory prefixStreamRead ∧
                                          UnaryHistory consumer ∧
                                            Cont sealClassifier witnessBudget prefixRead ∧
                                              Cont prefixRead streamReg prefixStreamRead ∧
                                                Cont prefixStreamRead terminalRead consumer ∧
                                                  SemanticNameCert
                                                    (fun row : BHist =>
                                                      hsame row consumer ∧ UnaryHistory row)
                                                    (fun row : BHist =>
                                                      hsame row prefixRead ∨
                                                        hsame row prefixStreamRead ∨
                                                          hsame row consumer)
                                                    (fun row : BHist =>
                                                      hsame row consumer ∧
                                                        PkgSig bundle consumer pkg)
                                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro limitSealUnary classifierUnary witnessUnary synchronizerUnary windowUnary readbackUnary
    dyadicUnary terminalUnary sealRoute witnessRoute streamRoute terminalRoute prefixRoute
    prefixStreamRoute consumerRoute consumerPkg
  have sealClassifierUnary : UnaryHistory sealClassifier :=
    unary_cont_closed limitSealUnary classifierUnary sealRoute
  have witnessBudgetUnary : UnaryHistory witnessBudget :=
    unary_cont_closed witnessUnary synchronizerUnary witnessRoute
  have streamRegUnary : UnaryHistory streamReg :=
    unary_cont_closed windowUnary readbackUnary streamRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed dyadicUnary terminalUnary terminalRoute
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed sealClassifierUnary witnessBudgetUnary prefixRoute
  have prefixStreamReadUnary : UnaryHistory prefixStreamRead :=
    unary_cont_closed prefixReadUnary streamRegUnary prefixStreamRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed prefixStreamReadUnary terminalReadUnary consumerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row prefixRead ∨ hsame row prefixStreamRead ∨ hsame row consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact
    ⟨rfl, prefixReadUnary, prefixStreamReadUnary, consumerUnary, prefixRoute,
      prefixStreamRoute, consumerRoute, cert⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
