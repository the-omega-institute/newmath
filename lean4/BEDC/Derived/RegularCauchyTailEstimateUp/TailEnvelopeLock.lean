import BEDC.Derived.RegularCauchyTailEstimateUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateCarrier_tail_envelope_lock
    {M W D R E H C P N envelopeRead sealRead : BHist} :
    UnaryHistory M →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory R →
            UnaryHistory E →
              hsame H (append M W) →
                Cont M W envelopeRead →
                  Cont envelopeRead D R →
                    Cont R E sealRead →
                      Cont C P N →
                        UnaryHistory envelopeRead ∧
                          UnaryHistory R ∧
                            UnaryHistory sealRead ∧
                              hsame H (append M W) ∧
                                Cont M W envelopeRead ∧
                                  Cont envelopeRead D R ∧
                                    Cont R E sealRead ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory append
  intro hM hW hD hR hE hH hEnvelope hReadback hSeal hRoute
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed hM hW hEnvelope
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed envelopeUnary hD hReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary hE hSeal
  exact
    ⟨envelopeUnary, readbackUnary, sealUnary, hH, hEnvelope, hReadback, hSeal,
      hRoute⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
