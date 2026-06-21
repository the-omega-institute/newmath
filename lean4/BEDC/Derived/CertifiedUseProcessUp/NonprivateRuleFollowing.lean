import BEDC.Derived.CertifiedUseProcessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertifiedUseProcessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CertifiedUseProcess_nonprivate_rule_following
    {use rule process refusal transport replay provenance name rejected : BHist} :
    CertifiedUseProcessUp →
      UnaryHistory use →
        UnaryHistory rule →
          UnaryHistory refusal →
            Cont use rule process →
              Cont process refusal replay →
                hsame transport (append use rule) →
                  Cont refusal rule rejected →
                    UnaryHistory process ∧ UnaryHistory replay ∧ UnaryHistory rejected ∧
                      Cont use rule process ∧ Cont process refusal replay ∧
                        hsame transport (append use rule) := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory
  intro carrier useUnary ruleUnary refusalUnary useRuleRoute processRefusalRoute
    transportSame refusalRuleRoute
  cases carrier
  have processUnary : UnaryHistory process :=
    unary_cont_closed useUnary ruleUnary useRuleRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed processUnary refusalUnary processRefusalRoute
  have rejectedUnary : UnaryHistory rejected :=
    unary_cont_closed refusalUnary ruleUnary refusalRuleRoute
  exact
    ⟨processUnary, replayUnary, rejectedUnary, useRuleRoute, processRefusalRoute,
      transportSame⟩

end BEDC.Derived.CertifiedUseProcessUp
