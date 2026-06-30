import BEDC.Derived.CauchyWitnessGluingUp

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyWitnessGluingCarrier_witness_ledger_exactness
    {ledger tail synchronizer classifier stream regular dyadic realSeal edge transport route
      provenance localName witnessRead : BHist} :
    CauchyWitnessGluingCarrier ledger tail synchronizer classifier stream regular dyadic realSeal
        edge transport route provenance localName ->
      Cont edge route witnessRead ->
        UnaryHistory ledger ∧ UnaryHistory tail ∧ UnaryHistory synchronizer ∧
          UnaryHistory classifier ∧ UnaryHistory edge ∧ UnaryHistory witnessRead ∧
            Cont ledger tail edge ∧ Cont synchronizer classifier route ∧
              Cont edge route witnessRead ∧ hsame transport (append edge route) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier edgeRouteWitness
  obtain
    ⟨ledgerUnary, tailUnary, synchronizerUnary, classifierUnary, _streamUnary, _regularUnary,
      _dyadicUnary, _realSealUnary, edgeUnary, _transportUnary, ledgerTailEdge,
      synchronizerClassifierRoute, _streamDyadicRegular, _regularRealSealEdge,
      transportRoute⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed synchronizerUnary classifierUnary synchronizerClassifierRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed edgeUnary routeUnary edgeRouteWitness
  exact
    ⟨ledgerUnary, tailUnary, synchronizerUnary, classifierUnary, edgeUnary, witnessReadUnary,
      ledgerTailEdge, synchronizerClassifierRoute, edgeRouteWitness, transportRoute⟩

end BEDC.Derived.CauchyWitnessGluingUp
