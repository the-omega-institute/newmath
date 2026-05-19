import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPhaseRealSourceWindowExhaustion
    {Z S M R Q H C P N ratRead realRead regSeqRead zeroStrip modulusRead
      windowRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStrip ->
        Cont M R ratRead ->
          Cont ratRead Q realRead ->
            Cont realRead H regSeqRead ->
              Cont regSeqRead C modulusRead ->
                Cont modulusRead P windowRead ->
                  UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                    UnaryHistory Q ∧ UnaryHistory zeroStrip ∧ UnaryHistory ratRead ∧
                      UnaryHistory realRead ∧ UnaryHistory regSeqRead ∧
                        UnaryHistory modulusRead ∧ UnaryHistory windowRead ∧
                          hsame H (append Z S) ∧ Cont Z S zeroStrip ∧
                            Cont M R ratRead ∧ Cont ratRead Q realRead ∧
                              Cont realRead H regSeqRead ∧ Cont regSeqRead C modulusRead ∧
                                Cont modulusRead P windowRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroStripRoute ratReadRoute realReadRoute regSeqReadRoute
    modulusReadRoute windowReadRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have unaryH : UnaryHistory H :=
    unary_transport
      (unary_cont_closed unaryZ unaryS (cont_intro rfl))
      (hsame_symm routeClosure.right.right.right)
  have zeroStripUnary : UnaryHistory zeroStrip :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have ratReadUnary : UnaryHistory ratRead :=
    unary_cont_closed unaryM unaryR ratReadRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed ratReadUnary routeClosure.left realReadRoute
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed realReadUnary unaryH regSeqReadRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed regSeqReadUnary routeClosure.right.left modulusReadRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed modulusReadUnary unaryP windowReadRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, zeroStripUnary, ratReadUnary,
      realReadUnary, regSeqReadUnary, modulusReadUnary, windowReadUnary,
      routeClosure.right.right.right, zeroStripRoute, ratReadRoute, realReadRoute,
      regSeqReadRoute, modulusReadRoute, windowReadRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
