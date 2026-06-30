import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CriticalLineWitnessFixedStripSourceTuple
    (Z S M R Q H C P N : BHist) : Prop :=
  UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
    UnaryHistory P ∧ hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N

theorem CriticalLineWitnessFixedStripSourceTuple_route_closure
    {Z S M R Q H C P N readback : BHist} :
    CriticalLineWitnessFixedStripSourceTuple Z S M R Q H C P N ->
      Cont (append Z S) Q readback ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
            UnaryHistory readback ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N ∧ Cont (append Z S) Q readback := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro tuple readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    tuple
  have unaryZS : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (show Cont Z S (append Z S) from rfl)
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport unaryZS (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryReadback : UnaryHistory readback :=
    unary_cont_closed unaryZS unaryQ readbackRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, unaryReadback,
      sameH, routeQ, routeC, routeN, readbackRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
