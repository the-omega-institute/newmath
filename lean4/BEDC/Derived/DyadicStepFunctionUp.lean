import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicStepFunctionCarrier [AskSetup] [PackageSetup]
    (partition cells values reads refinement endpointLedger ledger route provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory partition ∧ UnaryHistory cells ∧ UnaryHistory values ∧ UnaryHistory reads ∧
    UnaryHistory refinement ∧ UnaryHistory endpointLedger ∧ UnaryHistory ledger ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont partition cells values ∧ Cont values reads refinement ∧
          Cont refinement endpointLedger ledger ∧ Cont route provenance nameRow ∧
            PkgSig bundle nameRow pkg

theorem DyadicStepFunctionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {partition cells values reads refinement endpointLedger ledger route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger route
        provenance nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger
            route provenance nameRow bundle pkg ∧ hsame row nameRow)
        (fun _row : BHist =>
          DyadicStepFunctionCarrier partition cells values reads refinement endpointLedger ledger
            route provenance nameRow bundle pkg ∧ Cont partition cells values ∧
              Cont refinement endpointLedger ledger ∧ Cont route provenance nameRow)
        (fun row : BHist => PkgSig bundle nameRow pkg ∧ hsame row nameRow)
        hsame := by
  intro carrier
  have carrierPacket := carrier
  obtain ⟨_partitionUnary, _cellsUnary, _valuesUnary, _readsUnary, _refinementUnary,
    _endpointLedgerUnary, _ledgerUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    partitionCellsValues, _valuesReadsRefinement, refinementEndpointLedger,
    routeProvenanceNameRow, nameRowPkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameRow (And.intro carrierPacket (hsame_refl nameRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, partitionCellsValues, refinementEndpointLedger,
          routeProvenanceNameRow⟩
    ledger_sound := by
      intro _row source
      exact ⟨nameRowPkg, source.right⟩
  }

end BEDC.Derived.DyadicStepFunctionUp
