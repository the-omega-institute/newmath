import BEDC.FKernel.Gap

/-! Typed naming certificates license derived interfaces through five certified fields. -/
namespace BEDC.FKernel.NameCert

class NameCertSetup where
  DerivedName : Type
  SourceSpec : Type
  PatternSpec : Type
  ClassifierSpec : Type
  StabilityCert : Type
  LedgerPolicy : Type

section Cert

variable [N : NameCertSetup]

abbrev DerivedName : Type := N.DerivedName
abbrev SourceSpec : Type := N.SourceSpec
abbrev PatternSpec : Type := N.PatternSpec
abbrev ClassifierSpec : Type := N.ClassifierSpec
abbrev StabilityCert : Type := N.StabilityCert
abbrev LedgerPolicy : Type := N.LedgerPolicy

inductive NameCert (N : DerivedName) : Prop where
  | mk :
      SourceSpec →
      PatternSpec →
      ClassifierSpec →
      StabilityCert →
      LedgerPolicy →
      NameCert N

theorem derived_interfaces_require_certificates {n : DerivedName} :
    NameCert n -> Nonempty (NameCert n) := by
  intro cert
  exact ⟨cert⟩

theorem derived_interfaces_have_ledger {name : DerivedName} :
    NameCert name -> Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact Nonempty.intro ledger

end Cert

theorem ledger_witness_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → ∃ _ledger : LedgerPolicy, True := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact ⟨ledger, True.intro⟩

theorem NameCert_add_activation [NameCertSetup] {name : DerivedName}
    (source : SourceSpec)
    (pattern : PatternSpec)
    (classifier : ClassifierSpec)
    (stability : StabilityCert)
    (ledger : LedgerPolicy) : NameCert name := by
  exact NameCert.mk source pattern classifier stability ledger

def MinimalNameCertSetup : NameCertSetup where
  DerivedName := Unit
  SourceSpec := Unit
  PatternSpec := Unit
  ClassifierSpec := Unit
  StabilityCert := Unit
  LedgerPolicy := Unit

end BEDC.FKernel.NameCert
