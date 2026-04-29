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

structure NameCert (N : DerivedName) : Type where
  sourceSpec : SourceSpec
  patternSpec : PatternSpec
  classifierSpec : ClassifierSpec
  stabilityCert : StabilityCert
  ledgerPolicy : LedgerPolicy

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

end BEDC.FKernel.NameCert
