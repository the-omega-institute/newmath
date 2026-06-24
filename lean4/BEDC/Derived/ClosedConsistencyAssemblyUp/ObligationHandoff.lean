import BEDC.Derived.ClosedConsistencyAssemblyUp.Classifier

namespace BEDC.Derived.ClosedConsistencyAssemblyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ClosedConsistencyAssemblyObligationHandoff
    {closedness typing endpoint exclusion boundary obstruction ledger route provenance name
      assemblyRead handoffRead : BHist} :
    ClosedConsistencyAssemblyClassifier closedness typing endpoint exclusion boundary obstruction
        ledger route provenance name assemblyRead →
      Cont assemblyRead name handoffRead →
        UnaryHistory handoffRead ∧ Cont closedness typing endpoint ∧
          Cont endpoint exclusion boundary ∧ Cont boundary obstruction ledger ∧
            Cont ledger route assemblyRead ∧ Cont assemblyRead name handoffRead ∧
              hsame provenance (append route name) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classifier handoffRoute
  obtain ⟨_endpointUnary, _boundaryUnary, _ledgerUnary, assemblyUnary, closednessRoute,
    endpointRoute, boundaryRoute, ledgerRoute, provenanceRoute⟩ :=
    ClosedConsistencyAssemblyClassifier_route_obligations classifier
  obtain ⟨_closednessUnary, _typingUnary, _exclusionUnary, _obstructionUnary, _routeUnary,
    nameUnary, _closednessTypingRoute, _endpointExclusionRoute, _boundaryObstructionRoute,
    _ledgerAssemblyRoute, _provenanceRoute⟩ := classifier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed assemblyUnary nameUnary handoffRoute
  exact
    ⟨handoffUnary, closednessRoute, endpointRoute, boundaryRoute, ledgerRoute,
      handoffRoute, provenanceRoute⟩

end BEDC.Derived.ClosedConsistencyAssemblyUp
