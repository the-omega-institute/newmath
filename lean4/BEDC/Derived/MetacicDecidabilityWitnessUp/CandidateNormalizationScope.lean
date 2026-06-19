import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessCarrier_candidate_normalization_scope
    {T S B F R H C P N typingRead sameRead boundedRead normalRead scopeRead : BHist} :
    UnaryHistory T →
      UnaryHistory S →
        UnaryHistory B →
          UnaryHistory F →
            UnaryHistory R →
              hsame H (append T S) →
                Cont T S typingRead →
                  Cont typingRead S sameRead →
                    Cont sameRead B boundedRead →
                      Cont boundedRead F normalRead →
                        Cont normalRead R scopeRead →
                          Cont C P N →
                            UnaryHistory typingRead ∧
                              UnaryHistory sameRead ∧
                                UnaryHistory boundedRead ∧
                                  UnaryHistory normalRead ∧
                                    UnaryHistory scopeRead ∧
                                      hsame H (append T S) ∧
                                        Cont T S typingRead ∧
                                          Cont typingRead S sameRead ∧
                                            Cont sameRead B boundedRead ∧
                                              Cont boundedRead F normalRead ∧
                                                Cont normalRead R scopeRead ∧
                                                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory append
  intro hT hS hB hF hR hH hTyping hSame hBounded hNormal hScope hReplay
  have typingUnary : UnaryHistory typingRead :=
    unary_cont_closed hT hS hTyping
  have sameUnary : UnaryHistory sameRead :=
    unary_cont_closed typingUnary hS hSame
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed sameUnary hB hBounded
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed boundedUnary hF hNormal
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed normalUnary hR hScope
  exact
    ⟨typingUnary, sameUnary, boundedUnary, normalUnary, scopeUnary, hH, hTyping,
      hSame, hBounded, hNormal, hScope, hReplay⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
