import BEDC.Derived.CalculusUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CalculusIntegralFiniteSumObligation
    {E R D _L J H C P N integralRead integralPublic : BHist} :
    UnaryHistory E →
      UnaryHistory R →
        UnaryHistory D →
          UnaryHistory J →
            UnaryHistory C →
              UnaryHistory P →
                UnaryHistory N →
                  Cont R D integralRead →
                    Cont integralRead J integralPublic →
                      hsame H (append P N) →
                        UnaryHistory integralPublic ∧ Cont R D integralRead ∧
                          Cont integralRead J integralPublic ∧ hsame H (append P N) := by
  -- BEDC touchpoint anchor: CalculusUp BHist Cont hsame UnaryHistory append
  intro _eUnary rUnary dUnary jUnary _cUnary _pUnary _nUnary readCont publicCont hsameHPN
  have readUnary : UnaryHistory integralRead :=
    unary_cont_closed rUnary dUnary readCont
  have publicUnary : UnaryHistory integralPublic :=
    unary_cont_closed readUnary jUnary publicCont
  exact ⟨publicUnary, readCont, publicCont, hsameHPN⟩

end BEDC.Derived.CalculusUp
