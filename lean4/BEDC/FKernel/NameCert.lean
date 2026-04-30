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

omit N in
theorem derived_interfaces_have_stability [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty StabilityCert := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact Nonempty.intro stability

theorem nameCert_witnesses_from_cert {name : DerivedName} :
    NameCert name ->
      exists source : SourceSpec,
      exists pattern : PatternSpec,
      exists classifier : ClassifierSpec,
      exists stability : StabilityCert,
      exists ledger : LedgerPolicy, True := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact ⟨source, pattern, classifier, stability, ledger, True.intro⟩

end Cert

theorem ledger_witness_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → ∃ _ledger : LedgerPolicy, True := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact ⟨ledger, True.intro⟩

theorem nameCert_field_witnesses [NameCertSetup] {name : DerivedName} :
    NameCert name ->
      Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec /\
        Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact And.intro
        (Nonempty.intro source)
        (And.intro
          (Nonempty.intro pattern)
          (And.intro
            (Nonempty.intro classifier)
            (And.intro
              (Nonempty.intro stability)
              (Nonempty.intro ledger))))

theorem NameCert_add_activation [NameCertSetup] {name : DerivedName}
    (source : SourceSpec)
    (pattern : PatternSpec)
    (classifier : ClassifierSpec)
    (stability : StabilityCert)
    (ledger : LedgerPolicy) : NameCert name := by
  exact NameCert.mk source pattern classifier stability ledger

theorem add_like_behavior_certified_not_operation [NameCertSetup] {name : DerivedName}
    (source : SourceSpec)
    (pattern : PatternSpec)
    (classifier : ClassifierSpec)
    (stability : StabilityCert)
    (ledger : LedgerPolicy) :
    NameCert name ∧ Nonempty StabilityCert := by
  constructor
  · exact NameCert.mk source pattern classifier stability ledger
  · exact Nonempty.intro stability

theorem stable_transform_descends_to_packages
    {Source Target Ledger : Type}
    {sourceSame : Source → Source → Prop}
    {targetSame : Target → Target → Prop}
    (cert :
      { map : Source → Target //
        (∀ {a b : Source}, sourceSame a b → targetSame (map a) (map b)) ∧
          Nonempty Ledger })
    {a b : Source} :
    sourceSame a b → targetSame (cert.val a) (cert.val b) := by
  intro same
  cases cert with
  | mk map certData =>
      cases certData with
      | intro desc _ledger =>
          exact desc same

def MinimalNameCertSetup : NameCertSetup where
  DerivedName := Unit
  SourceSpec := Unit
  PatternSpec := Unit
  ClassifierSpec := Unit
  StabilityCert := Unit
  LedgerPolicy := Unit

end BEDC.FKernel.NameCert
