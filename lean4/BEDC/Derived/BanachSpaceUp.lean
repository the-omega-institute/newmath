import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_vector_norm_scope
    {V N M Q S R E Z H C P L vectorNormRead metricRead structuralRead : BHist} :
    UnaryHistory V ->
      UnaryHistory N ->
        UnaryHistory M ->
          UnaryHistory H ->
            UnaryHistory C ->
              Cont V N vectorNormRead ->
                Cont vectorNormRead M metricRead ->
                  Cont H C structuralRead ->
                    UnaryHistory vectorNormRead ∧
                      UnaryHistory metricRead ∧
                        UnaryHistory structuralRead ∧
                          banachSpaceFields (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                            [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory BanachSpaceUp
  intro vUnary nUnary mUnary hUnary cUnary vectorNormRoute metricRoute structuralRoute
  have vectorNormUnary : UnaryHistory vectorNormRead :=
    unary_cont_closed vUnary nUnary vectorNormRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed vectorNormUnary mUnary metricRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  exact ⟨vectorNormUnary, metricUnary, structuralUnary, rfl⟩

end BEDC.Derived.BanachSpaceUp
