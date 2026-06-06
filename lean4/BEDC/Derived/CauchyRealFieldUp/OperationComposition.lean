import BEDC.Derived.CauchyRealFieldUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRealFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyRealFieldCarrier_operation_composition
    {R S D Z A M I O H C P N addRead mulRead recipGate recipRead : BHist} :
    UnaryHistory R →
      UnaryHistory S →
        UnaryHistory D →
          UnaryHistory A →
            UnaryHistory M →
              UnaryHistory O →
                UnaryHistory I →
                  Cont R S addRead →
                    Cont addRead D mulRead →
                      Cont O I recipGate →
                        Cont recipGate D recipRead →
                          cauchyRealFieldFields
                              (CauchyRealFieldUp.mk R S D Z A M I O H C P N) =
                            [R, S, D, Z, A, M, I, O, H, C, P, N] ∧
                            UnaryHistory addRead ∧ UnaryHistory mulRead ∧
                              UnaryHistory recipGate ∧ UnaryHistory recipRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro regularUnary streamUnary dyadicUnary _addUnary _mulUnary orderUnary reciprocalUnary
    addRoute mulRoute reciprocalGate reciprocalRoute
  have addReadUnary : UnaryHistory addRead :=
    unary_cont_closed regularUnary streamUnary addRoute
  have mulReadUnary : UnaryHistory mulRead :=
    unary_cont_closed addReadUnary dyadicUnary mulRoute
  have recipGateUnary : UnaryHistory recipGate :=
    unary_cont_closed orderUnary reciprocalUnary reciprocalGate
  have recipReadUnary : UnaryHistory recipRead :=
    unary_cont_closed recipGateUnary dyadicUnary reciprocalRoute
  exact ⟨rfl, addReadUnary, mulReadUnary, recipGateUnary, recipReadUnary⟩

end BEDC.Derived.CauchyRealFieldUp
