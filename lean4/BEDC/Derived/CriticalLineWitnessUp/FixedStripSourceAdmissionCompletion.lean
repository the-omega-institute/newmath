import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_source_admission_completion
    {Z S M R Q H C P N sourceRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont N Q refusalRead ->
          hsame H (append Z S) ∧ UnaryHistory sourceRead ∧ UnaryHistory Q ∧
            UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory refusalRead ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N ∧ Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  exact
    ⟨routeClosure.right.right.right, sourceUnary, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, refusalUnary, routeQ, routeC, routeN, refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
