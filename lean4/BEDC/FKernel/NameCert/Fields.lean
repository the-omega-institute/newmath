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

end BEDC.FKernel.NameCert
