import BEDC.Derived.CalculusUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CalculusDerivativeContinuationObligation
    {E R D L _J H C P N derivativeRead derivativePublic : BHist} :
    UnaryHistory E →
      UnaryHistory R →
        UnaryHistory D →
          UnaryHistory L →
            UnaryHistory C →
              UnaryHistory P →
                UnaryHistory N →
                  Cont R D derivativeRead →
                    Cont derivativeRead L derivativePublic →
                      hsame H (append P N) →
                        UnaryHistory derivativePublic ∧ Cont R D derivativeRead ∧
                          Cont derivativeRead L derivativePublic ∧ hsame H (append P N) := by
  -- BEDC touchpoint anchor: CalculusUp BHist Cont hsame UnaryHistory append
  intro _eUnary rUnary dUnary lUnary _cUnary _pUnary _nUnary readCont publicCont hsameHPN
  have readUnary : UnaryHistory derivativeRead :=
    unary_cont_closed rUnary dUnary readCont
  have publicUnary : UnaryHistory derivativePublic :=
    unary_cont_closed readUnary lUnary publicCont
  exact ⟨publicUnary, readCont, publicCont, hsameHPN⟩

end BEDC.Derived.CalculusUp
