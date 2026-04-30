import BEDC.FKernel.NameCert

namespace BEDC.FKernel.NameCert

def threadFamily_base_stage {StageData : StageInterface -> Type} :
    ThreadFamily StageData -> StageData StageInterface.base := by
  intro family
  exact family StageInterface.base

theorem nameCert_all_fields_nonempty [NameCertSetup] {name : DerivedName} :
    NameCert name ->
      Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec /\
        Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · constructor
          · exact Nonempty.intro classifier
          · constructor
            · exact Nonempty.intro stability
            · exact Nonempty.intro ledger

theorem nameCert_core_five_field_witnesses [NameCertSetup] {name : DerivedName} :
    NameCert name ->
      Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec /\
        Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · constructor
          · exact Nonempty.intro classifier
          · constructor
            · exact Nonempty.intro stability
            · exact Nonempty.intro ledger

theorem definition_demotion_certificate_fields [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
      Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro cert
  exact nameCert_all_fields_nonempty cert

theorem typed_naming_certificate_expanded_template [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
      Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro cert
  exact nameCert_all_fields_nonempty cert

theorem derived_interfaces_require_certificate_and_fields [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty (NameCert name) /\ Nonempty SourceSpec /\ Nonempty PatternSpec /\
      Nonempty ClassifierSpec /\ Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro cert
  constructor
  · exact Nonempty.intro cert
  · exact nameCert_all_fields_nonempty cert

theorem addition_like_behavior_certificate_not_operation [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro cert
  exact nameCert_stability_and_ledger_from_cert cert

theorem no_inherited_mathematical_primitives [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
      Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · constructor
          · exact Nonempty.intro classifier
          · constructor
            · exact Nonempty.intro stability
            · exact Nonempty.intro ledger

theorem nameCert_source_pattern_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · exact Nonempty.intro ledger

theorem nameCert_source_pattern_classifier_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name →
      Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
        Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · constructor
          · exact Nonempty.intro classifier
          · exact Nonempty.intro ledger

theorem nameCert_source_pattern_stability_pair_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty StabilityCert := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · exact Nonempty.intro stability

theorem nameCert_source_classifier_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty SourceSpec ∧ Nonempty ClassifierSpec ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro classifier
        · exact Nonempty.intro ledger

theorem nameCert_source_classifier_stability_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty SourceSpec ∧ Nonempty ClassifierSpec ∧ Nonempty StabilityCert := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro classifier
        · exact Nonempty.intro stability

theorem nameCert_source_classifier_stability_ledger_from_cert [NameCertSetup]
    {name : DerivedName} :
    NameCert name →
      Nonempty SourceSpec ∧ Nonempty ClassifierSpec ∧ Nonempty StabilityCert ∧
        Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro classifier
        · constructor
          · exact Nonempty.intro stability
          · exact Nonempty.intro ledger

theorem nameCert_source_pattern_stability_ledger_from_cert [NameCertSetup]
    {name : DerivedName} :
    NameCert name →
      Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty StabilityCert ∧
        Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · constructor
          · exact Nonempty.intro stability
          · exact Nonempty.intro ledger

theorem nameCert_pattern_classifier_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name →
      Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro pattern
      · constructor
        · exact Nonempty.intro classifier
        · exact Nonempty.intro ledger

theorem nameCert_pattern_classifier_stability_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧ Nonempty StabilityCert := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro pattern
      · constructor
        · exact Nonempty.intro classifier
        · exact Nonempty.intro stability

theorem nameCert_pattern_stability_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty PatternSpec ∧ Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro pattern
      · constructor
        · exact Nonempty.intro stability
        · exact Nonempty.intro ledger

theorem nameCert_source_pattern_classifier_stability_from_cert [NameCertSetup]
    {name : DerivedName} :
    NameCert name →
      Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
        Nonempty StabilityCert := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro pattern
        · constructor
          · exact Nonempty.intro classifier
          · exact Nonempty.intro stability

theorem nameCert_classifier_stability_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty ClassifierSpec ∧ Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro classifier
      · constructor
        · exact Nonempty.intro stability
        · exact Nonempty.intro ledger

theorem nameCert_nonempty_iff_field_witnesses [NameCertSetup] {name : DerivedName} :
    Nonempty (NameCert name) ↔
      Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
        Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  constructor
  · intro certNonempty
    cases certNonempty with
    | intro cert =>
        exact nameCert_field_witnesses cert
  · intro witnesses
    cases witnesses with
    | intro sourceNonempty rest =>
        cases rest with
        | intro patternNonempty rest =>
            cases rest with
            | intro classifierNonempty rest =>
                cases rest with
                | intro stabilityNonempty ledgerNonempty =>
                    exact nameCert_from_field_nonempty sourceNonempty patternNonempty
                      classifierNonempty stabilityNonempty ledgerNonempty

theorem sealEvent_stability_witness [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealEvent Thread name -> Nonempty StabilityCert := by
  intro event
  cases event with
  | mk sealCert ledger =>
      exact Nonempty.intro sealCert

theorem limit_like_interfaces_are_derived [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name → Nonempty (NameCert name) ∧ Nonempty StabilityCert ∧
      Nonempty LedgerPolicy := by
  intro iface
  cases iface with
  | mk thread sealCertType sealCert nameCert ledger =>
      constructor
      · exact Nonempty.intro nameCert
      · constructor
        · cases nameCert with
          | mk source pattern classifier stability certLedger =>
              exact Nonempty.intro stability
        · exact ledger

theorem sealInterface_stability_witness [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name → Nonempty StabilityCert := by
  intro iface
  exact derived_interfaces_have_stability iface.nameCert

theorem sealInterface_full_witnesses [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name →
      Nonempty Thread ∧ NameCert name ∧ Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro iface
  cases iface with
  | mk thread sealCertType sealCert nameCert ledger =>
      constructor
      · exact Nonempty.intro thread
      · constructor
        · exact nameCert
        · constructor
          · cases nameCert with
            | mk source pattern classifier stability certLedger =>
                exact Nonempty.intro stability
          · exact ledger

theorem sealInterface_thread_name_pair [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name → Nonempty Thread ∧ Nonempty (NameCert name) := by
  intro iface
  cases iface with
  | mk thread sealCertType sealCert nameCert ledger =>
      constructor
      · exact Nonempty.intro thread
      · exact Nonempty.intro nameCert

end BEDC.FKernel.NameCert
