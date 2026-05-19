import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_realpart_modulus_stability
    {Z S M R Q H C P N R' M' transportedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      hsame R R' ->
        hsame M M' ->
          Cont M' R' transportedRead ->
            UnaryHistory R' ∧ UnaryHistory M' ∧ UnaryHistory transportedRead ∧
              hsame H (append Z S) ∧ Cont M R Q ∧ Cont M' R' transportedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sameR sameM transportedRoute
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryR' : UnaryHistory R' :=
    unary_transport unaryR sameR
  have unaryM' : UnaryHistory M' :=
    unary_transport unaryM sameM
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed unaryM' unaryR' transportedRoute
  exact ⟨unaryR', unaryM', transportedUnary, sameH, routeQ, transportedRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
