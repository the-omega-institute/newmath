import BEDC.Derived.LimitUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LimitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LimitRegSeqRatBishopHandoff
    {S R D A T C H P N readbackRead dyadicRead sealRead transportRead : BHist} :
    UnaryHistory S → UnaryHistory R → UnaryHistory D → UnaryHistory A → UnaryHistory T →
      Cont S R readbackRead → Cont readbackRead D dyadicRead →
        Cont dyadicRead A sealRead → Cont sealRead T transportRead →
          limitFields (LimitUp.mk S R D A T C H P N) = [S, R, D, A, T, C, H, P, N] ∧
            UnaryHistory readbackRead ∧ UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
              UnaryHistory transportRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryS unaryR unaryD unaryA unaryT readbackRoute dyadicRoute sealRoute transportRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed unaryS unaryR readbackRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryA sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary unaryT transportRoute
  exact ⟨rfl, readbackUnary, dyadicUnary, sealUnary, transportUnary⟩

end BEDC.Derived.LimitUp
