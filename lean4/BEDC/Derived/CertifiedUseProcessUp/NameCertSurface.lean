import BEDC.Derived.CertifiedUseProcessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertifiedUseProcessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CertifiedUseProcessNameCertSurface
    {use rule process refusal transport replay provenance name : BHist} :
    UnaryHistory use ->
      UnaryHistory rule ->
        UnaryHistory refusal ->
          CertifiedUseProcessUp ->
      Cont use rule process ->
        Cont process refusal replay ->
          hsame transport (append use rule) ->
            UnaryHistory use ∧ UnaryHistory rule ∧ UnaryHistory process ∧
              UnaryHistory refusal ∧ UnaryHistory replay ∧ hsame transport (append use rule) ∧
                Cont use rule process ∧ Cont process refusal replay := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory
  intro useUnary ruleUnary refusalUnary carrier useRuleRoute processRefusalRoute transportSame
  cases carrier
  have processUnary : UnaryHistory process :=
    unary_cont_closed useUnary ruleUnary useRuleRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed processUnary refusalUnary processRefusalRoute
  exact
    ⟨useUnary, ruleUnary, processUnary, refusalUnary, replayUnary, transportSame,
      useRuleRoute, processRefusalRoute⟩

end BEDC.Derived.CertifiedUseProcessUp
