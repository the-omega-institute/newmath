import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_namecert_source_lock
    {Z S M R Q H C P N sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory sourceRead ∧
          hsame H (append Z S) ∧ Cont Z S sourceRead ∧ Cont M R Q ∧ Cont Q H C ∧
            Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, sourceUnary, routeClosure.right.right.right,
      sourceRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
