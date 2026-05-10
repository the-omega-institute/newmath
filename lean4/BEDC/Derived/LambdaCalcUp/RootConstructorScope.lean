import BEDC.Derived.LambdaCalcUp.SubstitutionLedgerObligation

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.TreeUp

theorem LambdaCalcBHistTermPacketCarrier_root_constructor_scope
    {graph edge connected acyclic tag payload endpoint constructorLedger : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      Cont endpoint payload constructorLedger ->
        UnaryHistory tag ∧ UnaryHistory payload ∧ UnaryHistory endpoint ∧
          UnaryHistory constructorLedger ∧ hsame constructorLedger (append endpoint payload) ∧
            TreeBHistCarrier graph edge connected acyclic tag endpoint := by
  intro packet constructorRow
  have rows := TreeBHistCarrier_exactness_rows packet.left
  have constructorUnary : UnaryHistory constructorLedger :=
    unary_cont_closed packet.right.right.left packet.right.left constructorRow
  exact And.intro rows.right.right.right.right.right.right.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro constructorUnary
          (And.intro constructorRow packet.left))))

theorem LambdaCalcBHistTermPacketCarrier_root_substitution_scope
    {graph edge connected acyclic tag payload endpoint substTag substPayload substEndpoint varIndex
      ledger resultPayload provenance rootScope : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic substTag substPayload
          substEndpoint ->
        UnaryHistory varIndex ->
          UnaryHistory provenance ->
            Cont endpoint substEndpoint ledger ->
              Cont ledger varIndex resultPayload ->
                Cont resultPayload provenance rootScope ->
                  SemanticNameCert
                      (fun row : BHist =>
                        exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
                      (fun row : BHist =>
                        exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
                      (fun row : BHist =>
                        exists l : BHist, Cont endpoint substEndpoint l ∧ Cont l varIndex row)
                      hsame ∧
                    UnaryHistory ledger ∧ UnaryHistory resultPayload ∧ UnaryHistory rootScope ∧
                      hsame resultPayload (append (append endpoint substEndpoint) varIndex) ∧
                        hsame rootScope (append resultPayload provenance) := by
  intro packet substPacket varUnary provenanceUnary ledgerRow resultRow rootScopeRow
  have substitutionRows :=
    LambdaCalcBHistTermPacketCarrier_substitution_ledger_obligation packet substPacket varUnary
      ledgerRow resultRow
  have rootScopeUnary : UnaryHistory rootScope :=
    unary_cont_closed substitutionRows.right.right.left provenanceUnary rootScopeRow
  exact
    ⟨substitutionRows.left,
      substitutionRows.right.left,
      substitutionRows.right.right.left,
      rootScopeUnary,
      substitutionRows.right.right.right.left,
      rootScopeRow⟩

end BEDC.Derived.LambdaCalcUp
