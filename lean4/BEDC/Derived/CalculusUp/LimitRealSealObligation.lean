import BEDC.Derived.CalculusUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CalculusLimitRealSealObligation
    {E R D L J H _C P N derivativeRead integralRead limitRead : BHist} :
    UnaryHistory E →
      UnaryHistory R →
        UnaryHistory D →
          UnaryHistory L →
            UnaryHistory J →
              UnaryHistory E →
                Cont R D derivativeRead →
                  Cont derivativeRead L limitRead →
                    Cont R D integralRead →
                      Cont integralRead J limitRead →
                        hsame H (append P N) →
                          (UnaryHistory limitRead ∧ Cont R D derivativeRead ∧
                              Cont derivativeRead L limitRead ∧ hsame H (append P N)) ∧
                            (UnaryHistory limitRead ∧ Cont R D integralRead ∧
                              Cont integralRead J limitRead ∧ hsame H (append P N)) := by
  -- BEDC touchpoint anchor: CalculusUp BHist Cont hsame UnaryHistory append
  intro _eUnary rUnary dUnary lUnary jUnary _eUnaryAgain
    derivativeReadCont derivativeLimitCont integralReadCont integralLimitCont hsameHPN
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed rUnary dUnary derivativeReadCont
  have derivativeLimitUnary : UnaryHistory limitRead :=
    unary_cont_closed derivativeReadUnary lUnary derivativeLimitCont
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed rUnary dUnary integralReadCont
  have integralLimitUnary : UnaryHistory limitRead :=
    unary_cont_closed integralReadUnary jUnary integralLimitCont
  exact
    ⟨⟨derivativeLimitUnary, derivativeReadCont, derivativeLimitCont, hsameHPN⟩,
      ⟨integralLimitUnary, integralReadCont, integralLimitCont, hsameHPN⟩⟩

end BEDC.Derived.CalculusUp
