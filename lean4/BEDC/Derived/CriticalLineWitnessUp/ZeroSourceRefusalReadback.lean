import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_source_refusal_readback
    {Z S M R Q H C P N zeroRead modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead M modulusRead ->
          Cont modulusRead Q refusalRead ->
            UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧ UnaryHistory refusalRead ∧
              Cont Z S zeroRead ∧ Cont zeroRead M modulusRead ∧
                Cont modulusRead Q refusalRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame UnaryHistory
  intro packet zeroRoute modulusRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zeroUnary _unaryM modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed modulusUnary routeClosure.left refusalRoute
  exact
    ⟨zeroUnary, modulusUnary, refusalUnary, zeroRoute, modulusRoute, refusalRoute, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
