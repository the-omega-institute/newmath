import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupBHistCarrier
    (groupSource topologySource product inverse neighbourhood ledger provenance : BHist) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
    UnaryHistory neighbourhood ∧ Cont groupSource topologySource product ∧
      Cont product inverse ledger ∧ Cont ledger neighbourhood provenance

theorem TopGroupBHistCarrier_scope
    {groupSource topologySource product inverse neighbourhood ledger provenance : BHist} :
    TopGroupBHistCarrier groupSource topologySource product inverse neighbourhood ledger
        provenance →
      GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
        UnaryHistory groupSource ∧ UnaryHistory topologySource ∧ UnaryHistory product ∧
          UnaryHistory neighbourhood ∧
            Cont groupSource topologySource product ∧ Cont product inverse ledger ∧
              Cont ledger neighbourhood provenance := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier
  obtain ⟨groupCarrier, topologyCarrier, neighbourhoodUnary, groupTopologyProduct,
    productInverseLedger, ledgerNeighbourhoodProvenance⟩ := carrier
  have groupUnary : UnaryHistory groupSource :=
    unary_transport unary_empty (hsame_symm groupCarrier)
  have topologyUnary : UnaryHistory topologySource :=
    unary_transport unary_empty (hsame_symm topologyCarrier)
  have productUnary : UnaryHistory product :=
    unary_cont_closed groupUnary topologyUnary groupTopologyProduct
  exact
    ⟨groupCarrier, topologyCarrier, groupUnary, topologyUnary, productUnary, neighbourhoodUnary,
      groupTopologyProduct, productInverseLedger, ledgerNeighbourhoodProvenance⟩

end BEDC.Derived.TopGroupUp
