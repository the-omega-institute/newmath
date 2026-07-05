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

theorem SubjectReductionBundleTraceCarrier_non_escape
    {bundle setup extraction ledger transport route provenance name directRead setupBundle
      setupRead : BHist} :
    SubjectReductionBundleTraceCarrier bundle setup extraction ledger transport route provenance name ->
      Cont bundle ledger directRead ->
        Cont setup extraction setupBundle ->
          Cont setupBundle ledger setupRead ->
            SemanticNameCert
                (fun row : BHist => hsame row setupRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row setupRead ∧ Cont bundle ledger directRead)
                (fun row : BHist => hsame row setupRead ∧ Cont setupBundle ledger setupRead)
                hsame ∧
              UnaryHistory directRead ∧ UnaryHistory setupRead ∧ Cont route provenance name := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet directRoute setupExtractionRoute setupLedgerRoute
  obtain ⟨bundleUnary, setupUnary, extractionUnary, ledgerUnary, _provenanceUnary,
    _transportSame, _ledgerTransportRoute, routeProvenanceName⟩ := packet
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
  exact ⟨cert, directReadUnary, setupReadUnary, routeProvenanceName⟩

theorem SubjectReductionBundleTraceCarrier_namecert_obligations
    {bundle setup extraction ledger transport route provenance name : BHist} :
    SubjectReductionBundleTraceCarrier bundle setup extraction ledger transport route provenance name ->
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row bundle ∨ hsame row setup ∨ hsame row extraction ∨ hsame row ledger ∨
            hsame row transport ∨ hsame row route ∨ hsame row provenance ∨ hsame row name)
        (fun row : BHist => hsame row name ∧ Cont ledger transport route ∧
          Cont route provenance name)
        hsame ∧ UnaryHistory bundle ∧ UnaryHistory setup ∧ UnaryHistory extraction ∧
          UnaryHistory ledger ∧ UnaryHistory route ∧ UnaryHistory name ∧
            Cont ledger transport route ∧ Cont route provenance name := by
  -- BEDC touchpoint anchor: BHist Cont append hsame SemanticNameCert UnaryHistory
  intro packet
  obtain ⟨bundleUnary, setupUnary, extractionUnary, ledgerUnary, provenanceUnary,
    transportSame, ledgerTransportRoute, routeProvenanceName⟩ := packet
  have appendUnary : UnaryHistory (append bundle setup) :=
    unary_append_closed bundleUnary setupUnary
  have transportUnary : UnaryHistory transport :=
    unary_transport_symm appendUnary transportSame
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have nameUnary : UnaryHistory name :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceName
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row bundle ∨ hsame row setup ∨ hsame row extraction ∨ hsame row ledger ∨
            hsame row transport ∨ hsame row route ∨ hsame row provenance ∨ hsame row name)
        (fun row : BHist => hsame row name ∧ Cont ledger transport route ∧
          Cont route provenance name)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerTransportRoute, routeProvenanceName⟩
  }
  exact
    ⟨cert, bundleUnary, setupUnary, extractionUnary, ledgerUnary, routeUnary, nameUnary,
      ledgerTransportRoute, routeProvenanceName⟩

theorem SubjectReductionBundleTraceCarrier_public_export
    {bundle setup extraction ledger transport route provenance name directRead setupBundle
      setupRead : BHist} :
    SubjectReductionBundleTraceCarrier bundle setup extraction ledger transport route provenance name ->
      Cont bundle ledger directRead ->
        Cont setup extraction setupBundle ->
          Cont setupBundle ledger setupRead ->
            SemanticNameCert
                (fun row : BHist => hsame row name ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row bundle ∨ hsame row setup ∨ hsame row extraction ∨
                    hsame row ledger ∨ hsame row transport ∨ hsame row route ∨
                      hsame row provenance ∨ hsame row name ∨ hsame row directRead ∨
                        hsame row setupRead)
                (fun row : BHist => hsame row name ∧ Cont ledger transport route ∧
                  Cont route provenance name)
                hsame ∧ UnaryHistory directRead ∧ UnaryHistory setupRead ∧
              Cont route provenance name := by
  -- BEDC touchpoint anchor: BHist Cont append hsame SemanticNameCert UnaryHistory
  intro packet directRoute setupExtractionRoute setupLedgerRoute
  obtain ⟨bundleUnary, setupUnary, extractionUnary, ledgerUnary, provenanceUnary,
    transportSame, ledgerTransportRoute, routeProvenanceName⟩ := packet
  have appendUnary : UnaryHistory (append bundle setup) :=
    unary_append_closed bundleUnary setupUnary
  have transportUnary : UnaryHistory transport :=
    unary_transport_symm appendUnary transportSame
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have nameUnary : UnaryHistory name :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceName
  have directReadUnary : UnaryHistory directRead :=
    unary_cont_closed bundleUnary ledgerUnary directRoute
  have setupBundleUnary : UnaryHistory setupBundle :=
    unary_cont_closed setupUnary extractionUnary setupExtractionRoute
  have setupReadUnary : UnaryHistory setupRead :=
    unary_cont_closed setupBundleUnary ledgerUnary setupLedgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bundle ∨ hsame row setup ∨ hsame row extraction ∨ hsame row ledger ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row name ∨ hsame row directRead ∨ hsame row setupRead)
          (fun row : BHist => hsame row name ∧ Cont ledger transport route ∧
            Cont route provenance name)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerTransportRoute, routeProvenanceName⟩
  }
  exact ⟨cert, directReadUnary, setupReadUnary, routeProvenanceName⟩

theorem SubjectReductionBundleTraceCarrier_obligation_route
    {bundle setup extraction ledger transport route provenance name directRead setupBundle
      setupRead : BHist} :
    SubjectReductionBundleTraceCarrier bundle setup extraction ledger transport route provenance name ->
      Cont bundle ledger directRead ->
        Cont setup extraction setupBundle ->
          Cont setupBundle ledger setupRead ->
            SemanticNameCert
                (fun row : BHist => hsame row name ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row bundle ∨ hsame row setup ∨ hsame row extraction ∨
                    hsame row ledger ∨ hsame row transport ∨ hsame row route ∨
                      hsame row provenance ∨ hsame row name ∨ hsame row directRead ∨
                        hsame row setupRead)
                (fun row : BHist => hsame row name ∧ Cont ledger transport route ∧
                  Cont route provenance name ∧ Cont setupBundle ledger setupRead)
                hsame ∧ UnaryHistory directRead ∧ UnaryHistory setupRead ∧
              Cont route provenance name := by
  -- BEDC touchpoint anchor: BHist Cont append hsame SemanticNameCert UnaryHistory
  intro packet directRoute setupExtractionRoute setupLedgerRoute
  obtain ⟨bundleUnary, setupUnary, extractionUnary, ledgerUnary, provenanceUnary,
    transportSame, ledgerTransportRoute, routeProvenanceName⟩ := packet
  have appendUnary : UnaryHistory (append bundle setup) :=
    unary_append_closed bundleUnary setupUnary
  have transportUnary : UnaryHistory transport :=
    unary_transport_symm appendUnary transportSame
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have nameUnary : UnaryHistory name :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceName
  have directReadUnary : UnaryHistory directRead :=
    unary_cont_closed bundleUnary ledgerUnary directRoute
  have setupBundleUnary : UnaryHistory setupBundle :=
    unary_cont_closed setupUnary extractionUnary setupExtractionRoute
  have setupReadUnary : UnaryHistory setupRead :=
    unary_cont_closed setupBundleUnary ledgerUnary setupLedgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bundle ∨ hsame row setup ∨ hsame row extraction ∨ hsame row ledger ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row name ∨ hsame row directRead ∨ hsame row setupRead)
          (fun row : BHist => hsame row name ∧ Cont ledger transport route ∧
            Cont route provenance name ∧ Cont setupBundle ledger setupRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerTransportRoute, routeProvenanceName, setupLedgerRoute⟩
  }
  exact ⟨cert, directReadUnary, setupReadUnary, routeProvenanceName⟩

end BEDC.Derived.SubjectReductionBundleTraceUp
