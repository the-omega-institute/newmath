import BEDC.Derived.CauchyWitnessGluingUp

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyWitnessGluingCarrier_scoped_route_tightening
    {ledger tail synchronizer classifier stream regular dyadic realSeal edge transport route
      provenance localName sealRead : BHist} :
    CauchyWitnessGluingCarrier ledger tail synchronizer classifier stream regular dyadic realSeal
        edge transport route provenance localName ->
      Cont synchronizer classifier sealRead ->
        UnaryHistory synchronizer ∧ UnaryHistory classifier ∧ UnaryHistory route ∧
          UnaryHistory sealRead ∧ Cont synchronizer classifier route ∧
            Cont synchronizer classifier sealRead ∧ hsame route sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier synchronizerClassifierSeal
  obtain
    ⟨_ledgerUnary, _tailUnary, synchronizerUnary, classifierUnary, _streamUnary,
      _regularUnary, _dyadicUnary, _realSealUnary, _edgeUnary, _transportUnary,
      _ledgerTailEdge, synchronizerClassifierRoute, _streamDyadicRegular,
      _regularRealSealEdge, _transportRoute⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed synchronizerUnary classifierUnary synchronizerClassifierRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed synchronizerUnary classifierUnary synchronizerClassifierSeal
  have routeSeal : hsame route sealRead :=
    cont_deterministic synchronizerClassifierRoute synchronizerClassifierSeal
  exact
    ⟨synchronizerUnary, classifierUnary, routeUnary, sealReadUnary,
      synchronizerClassifierRoute, synchronizerClassifierSeal, routeSeal⟩

end BEDC.Derived.CauchyWitnessGluingUp
