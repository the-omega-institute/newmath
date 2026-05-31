import BEDC.Derived.DyadicStepFunctionUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicStepFunctionUp.CommonRefinementRealRegseq

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.DyadicStepFunctionUp

theorem DyadicStepFunctionCarrier_common_refinement_real_regseq_correspondence
    [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance nameRow
      exposedRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg →
      Cont ledger route exposedRead →
        Cont exposedRead nameRow realRead →
          PkgSig bundle realRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cells ∨ hsame row refinement ∨ hsame row endpointLedger ∨
                    hsame row ledger ∨ hsame row exposedRead ∨ hsame row realRead)
                (fun row : BHist => hsame row realRead ∧ PkgSig bundle realRead pkg)
                hsame ∧
              UnaryHistory cells ∧ UnaryHistory refinement ∧ UnaryHistory endpointLedger ∧
                UnaryHistory ledger ∧ UnaryHistory exposedRead ∧ UnaryHistory realRead ∧
                  Cont refinement endpointLedger ledger ∧ Cont ledger route exposedRead ∧
                    Cont exposedRead nameRow realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier exposedRoute realRoute realPkg
  obtain ⟨_partitionUnary, cellsUnary, _valuesUnary, _readsUnary, refinementUnary,
    endpointLedgerUnary, ledgerUnary, routeUnary, _provenanceUnary, nameRowUnary,
    _partitionCellsValues, _valuesReadsRefinement, refinementEndpointLedger,
    _routeProvenanceNameRow, _nameRowPkg⟩ := carrier
  have exposedUnary : UnaryHistory exposedRead :=
    unary_cont_closed ledgerUnary routeUnary exposedRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed exposedUnary nameRowUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cells ∨ hsame row refinement ∨ hsame row endpointLedger ∨
              hsame row ledger ∨ hsame row exposedRead ∨ hsame row realRead)
          (fun row : BHist => hsame row realRead ∧ PkgSig bundle realRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRow.left
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, realPkg⟩
    }
  exact
    ⟨cert, cellsUnary, refinementUnary, endpointLedgerUnary, ledgerUnary, exposedUnary,
      realUnary, refinementEndpointLedger, exposedRoute, realRoute⟩

end BEDC.Derived.DyadicStepFunctionUp.CommonRefinementRealRegseq
