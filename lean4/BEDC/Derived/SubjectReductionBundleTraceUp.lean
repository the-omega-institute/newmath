import BEDC.Derived.SubjectReductionBundleTraceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionBundleTraceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def SubjectReductionBundleTraceCarrier
    (bundle setup extraction ledger transport route provenance name : BHist) : Prop :=
  UnaryHistory bundle ∧ UnaryHistory setup ∧ UnaryHistory extraction ∧
    UnaryHistory ledger ∧ UnaryHistory provenance ∧ hsame transport (append bundle setup) ∧
      Cont ledger transport route ∧ Cont route provenance name

theorem SubjectReductionBundleTraceCarrier_route_readback
    {bundle setup extraction ledger transport route provenance name directRead setupBundle
      setupRead : BHist} :
    SubjectReductionBundleTraceCarrier bundle setup extraction ledger transport route
        provenance name ->
      Cont bundle ledger directRead ->
        Cont setup extraction setupBundle ->
          Cont setupBundle ledger setupRead ->
            SemanticNameCert
                (fun row : BHist => hsame row setupRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row setupRead ∧ Cont bundle ledger directRead)
                (fun row : BHist => hsame row setupRead ∧ Cont setupBundle ledger setupRead)
                hsame ∧
              UnaryHistory bundle ∧ UnaryHistory setup ∧ UnaryHistory extraction ∧
                UnaryHistory ledger ∧ UnaryHistory directRead ∧ UnaryHistory setupBundle ∧
                  UnaryHistory setupRead ∧ hsame transport (append bundle setup) ∧
                    Cont bundle ledger directRead ∧ Cont setup extraction setupBundle ∧
                      Cont setupBundle ledger setupRead ∧ Cont ledger transport route ∧
                        Cont route provenance name := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet directRoute setupExtractionRoute setupLedgerRoute
  obtain ⟨bundleUnary, setupUnary, extractionUnary, ledgerUnary, provenanceUnary,
    transportSame, ledgerTransportRoute, routeProvenanceName⟩ := packet
  have directReadUnary : UnaryHistory directRead :=
    unary_cont_closed bundleUnary ledgerUnary directRoute
  have setupBundleUnary : UnaryHistory setupBundle :=
    unary_cont_closed setupUnary extractionUnary setupExtractionRoute
  have setupReadUnary : UnaryHistory setupRead :=
    unary_cont_closed setupBundleUnary ledgerUnary setupLedgerRoute
  have sourceAtSetupRead : hsame setupRead setupRead ∧ UnaryHistory setupRead :=
    ⟨hsame_refl setupRead, setupReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row setupRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row setupRead ∧ Cont bundle ledger directRead)
          (fun row : BHist => hsame row setupRead ∧ Cont setupBundle ledger setupRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro setupRead sourceAtSetupRead
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, directRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, setupLedgerRoute⟩
  }
  exact
    ⟨cert, bundleUnary, setupUnary, extractionUnary, ledgerUnary, directReadUnary,
      setupBundleUnary, setupReadUnary, transportSame, directRoute, setupExtractionRoute,
      setupLedgerRoute, ledgerTransportRoute, routeProvenanceName⟩

end BEDC.Derived.SubjectReductionBundleTraceUp
