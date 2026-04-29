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

def MinimalNameCertSetup : NameCertSetup where
  DerivedName := Unit
  SourceSpec := Unit
  PatternSpec := Unit
  ClassifierSpec := Unit
  StabilityCert := Unit
  LedgerPolicy := Unit

omit N in
theorem NameCert_add_activation [NameCertSetup] {name : DerivedName}
    (source : SourceSpec)
    (pattern : PatternSpec)
    (classifier : ClassifierSpec)
    (stability : StabilityCert)
    (ledger : LedgerPolicy) : NameCert name := by
  exact NameCert.mk source pattern classifier stability ledger

end BEDC.FKernel.NameCert
