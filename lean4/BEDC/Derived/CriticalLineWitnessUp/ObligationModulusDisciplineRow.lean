import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_obligation_modulus_discipline_row
    {Z S M R Q H C P N depthRead routedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R depthRead →
        Cont depthRead H routedRead →
          hsame routedRead C →
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory depthRead ∧
              UnaryHistory routedRead ∧ hsame depthRead Q ∧ hsame H (append Z S) ∧
                Cont M R depthRead ∧ Cont depthRead H routedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier depthRoute routedRoute _sameRouted
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, carrierDepthRoute,
    _carrierRoutedRoute, _carrierNameRoute⟩ := carrier
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have sameDepth : hsame depthRead Q :=
    cont_deterministic depthRoute carrierDepthRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have routedUnary : UnaryHistory routedRead :=
    unary_cont_closed depthUnary unaryH routedRoute
  have qUnary : UnaryHistory Q :=
    unary_transport depthUnary sameDepth
  exact
    ⟨unaryM, unaryR, qUnary, depthUnary, routedUnary, sameDepth, sameH, depthRoute,
      routedRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
