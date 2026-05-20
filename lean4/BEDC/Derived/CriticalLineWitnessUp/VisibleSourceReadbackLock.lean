import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_visible_source_readback_lock
    {Z S M R Q H C P N sourceRead comparisonRead downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R comparisonRead ->
          Cont N Q downstream ->
            hsame sourceRead H ∧ hsame comparisonRead Q ∧ UnaryHistory Z ∧
              UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory sourceRead ∧
                UnaryHistory comparisonRead ∧ UnaryHistory downstream ∧
                  hsame H (append Z S) ∧ Cont M R comparisonRead ∧
                    Cont N Q downstream := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet sourceRoute comparisonRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceSameAppend : hsame sourceRead (append Z S) :=
    cont_deterministic sourceRoute (cont_intro rfl)
  have sourceSameH : hsame sourceRead H :=
    hsame_trans sourceSameAppend (hsame_symm sameH)
  have comparisonSameQ : hsame comparisonRead Q :=
    cont_deterministic comparisonRoute routeQ
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed unaryN unaryQ downstreamRoute
  exact
    ⟨sourceSameH, comparisonSameQ, unaryZ, unaryS, unaryQ, sourceUnary, comparisonUnary,
      downstreamUnary, sameH, comparisonRoute, downstreamRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
