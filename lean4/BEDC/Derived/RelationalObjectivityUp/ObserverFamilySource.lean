import BEDC.Derived.RelationalObjectivityUp.TasteGate

namespace BEDC.Derived.RelationalObjectivityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RelationalObjectivityObserverFamilySource
    {F I A L T P N familyRead : BHist} :
    RelationalObjectivityCarrier F I A L T P N →
      Cont F I familyRead →
        UnaryHistory F ∧ UnaryHistory I ∧ UnaryHistory familyRead ∧
          Cont F I familyRead ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier familyRoute
  obtain ⟨familyUnary, invariantUnary, _anchorUnary, _ledgerUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _invariantAnchorTransport, _ledgerTransportName,
    _provenanceSelf⟩ := carrier
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed familyUnary invariantUnary familyRoute
  exact ⟨familyUnary, invariantUnary, familyReadUnary, familyRoute, hsame_refl N⟩

end BEDC.Derived.RelationalObjectivityUp
