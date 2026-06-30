import BEDC.Derived.ClosedConsistencyAssemblyUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedConsistencyAssemblyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ClosedConsistencyAssemblyClassifier
    (closedness typing endpoint exclusion boundary obstruction ledger route provenance name
      assemblyRead : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory closedness ∧ UnaryHistory typing ∧ UnaryHistory exclusion ∧
    UnaryHistory obstruction ∧ UnaryHistory route ∧ UnaryHistory name ∧
      Cont closedness typing endpoint ∧ Cont endpoint exclusion boundary ∧
        Cont boundary obstruction ledger ∧ Cont ledger route assemblyRead ∧
          hsame provenance (append route name)

theorem ClosedConsistencyAssemblyClassifier_route_obligations
    {closedness typing endpoint exclusion boundary obstruction ledger route provenance name
      assemblyRead : BHist} :
    ClosedConsistencyAssemblyClassifier closedness typing endpoint exclusion boundary obstruction
        ledger route provenance name assemblyRead →
      UnaryHistory endpoint ∧ UnaryHistory boundary ∧ UnaryHistory ledger ∧
        UnaryHistory assemblyRead ∧ Cont closedness typing endpoint ∧
          Cont endpoint exclusion boundary ∧ Cont boundary obstruction ledger ∧
            Cont ledger route assemblyRead ∧ hsame provenance (append route name) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro h
  exact
    match h with
    | ⟨closednessUnary, typingUnary, exclusionUnary, obstructionUnary, routeUnary, _nameUnary,
        closednessTypingRoute, endpointExclusionRoute, boundaryObstructionRoute, ledgerRoute,
        provenanceRoute⟩ =>
        let endpointUnary : UnaryHistory endpoint :=
          unary_cont_closed closednessUnary typingUnary closednessTypingRoute
        let boundaryUnary : UnaryHistory boundary :=
          unary_cont_closed endpointUnary exclusionUnary endpointExclusionRoute
        let ledgerUnary : UnaryHistory ledger :=
          unary_cont_closed boundaryUnary obstructionUnary boundaryObstructionRoute
        let assemblyUnary : UnaryHistory assemblyRead :=
          unary_cont_closed ledgerUnary routeUnary ledgerRoute
        ⟨endpointUnary, boundaryUnary, ledgerUnary, assemblyUnary, closednessTypingRoute,
          endpointExclusionRoute, boundaryObstructionRoute, ledgerRoute, provenanceRoute⟩

end BEDC.Derived.ClosedConsistencyAssemblyUp
