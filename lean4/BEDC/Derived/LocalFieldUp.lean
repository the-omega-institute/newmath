import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocalFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocalFieldValuedBHistCarrier [AskSetup] [PackageSetup]
    (field valuation residue unit completeness endpoint ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory field ∧ UnaryHistory valuation ∧ UnaryHistory residue ∧
    UnaryHistory unit ∧ UnaryHistory completeness ∧ Cont field valuation endpoint ∧
      Cont residue unit ledger ∧ Cont endpoint ledger provenance ∧ PkgSig bundle provenance pkg

theorem LocalFieldValuationClassifier_stability [AskSetup] [PackageSetup]
    {field valuation residue unit completeness endpoint ledger provenance field' valuation'
      residue' unit' endpoint' ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocalFieldValuedBHistCarrier field valuation residue unit completeness endpoint ledger
        provenance bundle pkg ->
      hsame field field' -> hsame valuation valuation' -> hsame residue residue' ->
        hsame unit unit' -> Cont field' valuation' endpoint' ->
          Cont residue' unit' ledger' -> Cont endpoint' ledger' provenance' ->
            PkgSig bundle provenance' pkg ->
              LocalFieldValuedBHistCarrier field' valuation' residue' unit' completeness
                  endpoint' ledger' provenance' bundle pkg ∧
                hsame endpoint endpoint' ∧ hsame ledger ledger' ∧ hsame provenance provenance' := by
  intro carrier sameField sameValuation sameResidue sameUnit endpointRow' ledgerRow'
  intro provenanceRow' pkgSig'
  have fieldUnary' : UnaryHistory field' := unary_transport carrier.left sameField
  have valuationUnary' : UnaryHistory valuation' :=
    unary_transport carrier.right.left sameValuation
  have residueUnary' : UnaryHistory residue' :=
    unary_transport carrier.right.right.left sameResidue
  have unitUnary' : UnaryHistory unit' :=
    unary_transport carrier.right.right.right.left sameUnit
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameField sameValuation carrier.right.right.right.right.right.left
      endpointRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameResidue sameUnit carrier.right.right.right.right.right.right.left
      ledgerRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameEndpoint sameLedger
      carrier.right.right.right.right.right.right.right.left provenanceRow'
  exact
    ⟨⟨fieldUnary', valuationUnary', residueUnary', unitUnary',
      carrier.right.right.right.right.left, endpointRow', ledgerRow', provenanceRow', pkgSig'⟩,
      sameEndpoint, sameLedger, sameProvenance⟩

theorem LocalFieldValuedBHistCarrier_residue_ledger_exactness [AskSetup] [PackageSetup]
    {field valuation residue unit completeness endpoint ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocalFieldValuedBHistCarrier field valuation residue unit completeness endpoint ledger
        provenance bundle pkg ->
      UnaryHistory residue ∧ UnaryHistory unit ∧ UnaryHistory ledger ∧
        UnaryHistory provenance ∧ hsame ledger (append residue unit) ∧
          hsame provenance (append endpoint ledger) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed
      (unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.right.right.left)
      ledgerUnary carrier.right.right.right.right.right.right.right.left
  exact
    ⟨carrier.right.right.left, carrier.right.right.right.left, ledgerUnary, provenanceUnary,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

theorem LocalFieldValuedBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {field valuation residue unit completeness endpoint ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocalFieldValuedBHistCarrier field valuation residue unit completeness endpoint ledger
        provenance bundle pkg ->
      SemanticNameCert (fun h : BHist => hsame h provenance)
          (fun h : BHist => hsame h provenance) (fun h : BHist => hsame h provenance) hsame ∧
        hsame endpoint (append field valuation) ∧ hsame ledger (append residue unit) ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  have endpointRow : Cont field valuation endpoint :=
    carrier.right.right.right.right.right.left
  have ledgerRow : Cont residue unit ledger :=
    carrier.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert (fun h : BHist => hsame h provenance)
          (fun h : BHist => hsame h provenance) (fun h : BHist => hsame h provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact hsame_trans (hsame_symm sameRows) carrierRow
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert (And.intro endpointRow (And.intro ledgerRow pkgSig))

theorem LocalFieldValuedBHistCarrier_bridge_boundary_exclusions [AskSetup] [PackageSetup]
    {field valuation residue unit completeness endpoint ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocalFieldValuedBHistCarrier field valuation residue unit completeness endpoint ledger
        provenance bundle pkg ->
      UnaryHistory endpoint ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
        hsame endpoint (append field valuation) ∧ hsame ledger (append residue unit) ∧
          hsame provenance (append endpoint ledger) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed endpointUnary ledgerUnary carrier.right.right.right.right.right.right.right.left
  exact
    ⟨endpointUnary, ledgerUnary, provenanceUnary,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

theorem LocalFieldValuedBHistCarrier_valued_field_consumer_threshold [AskSetup]
    [PackageSetup]
    {field valuation residue unit completeness endpoint ledger provenance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocalFieldValuedBHistCarrier field valuation residue unit completeness endpoint ledger
        provenance bundle pkg ->
      Cont provenance completeness consumer ->
        UnaryHistory consumer ∧ hsame consumer (append provenance completeness) ∧
          UnaryHistory field ∧ UnaryHistory valuation ∧ UnaryHistory residue ∧
            UnaryHistory unit ∧ UnaryHistory completeness ∧ hsame endpoint
              (append field valuation) ∧ hsame ledger (append residue unit) ∧
                hsame provenance (append endpoint ledger) ∧
                  PkgSig bundle provenance pkg := by
  intro carrier consumerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.right.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed endpointUnary ledgerUnary carrier.right.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed provenanceUnary carrier.right.right.right.right.left consumerRoute
  exact
    ⟨consumerUnary, consumerRoute, carrier.left, carrier.right.left, carrier.right.right.left,
      carrier.right.right.right.left, carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.LocalFieldUp
