import BEDC.FKernel.NameCert

namespace BEDC.FKernel.NameCert

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

end BEDC.FKernel.NameCert
