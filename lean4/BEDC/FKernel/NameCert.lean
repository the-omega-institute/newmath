import BEDC.FKernel.Gap

/-! Typed naming certificates license derived interfaces through five certified fields. -/
namespace BEDC.FKernel.NameCert

inductive StageInterface where
  | base : StageInterface

def ThreadFamily (StageData : StageInterface -> Type) : Type :=
  (stage : StageInterface) -> StageData stage

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

structure SealEvent (Thread : Type) (name : DerivedName) : Type where
  sealCert : StabilityCert
  ledger : LedgerPolicy

omit N in
theorem sealEvent_field_witnesses [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealEvent Thread name -> Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro event
  cases event with
  | mk sealCert ledger =>
      constructor
      · exact Nonempty.intro sealCert
      · exact Nonempty.intro ledger

structure SealInterface (Thread : Type) (name : DerivedName) : Type 1 where
  thread : Thread
  sealCertType : Type
  sealCert : Nonempty sealCertType
  nameCert : NameCert name
  ledger : Nonempty LedgerPolicy

omit N in
theorem sealInterface_thread_witness [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name -> Nonempty Thread := by
  intro iface
  exact Nonempty.intro iface.thread

omit N in
theorem sealInterface_field_witnesses [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name -> Nonempty Thread ∧ Nonempty (NameCert name) ∧ Nonempty LedgerPolicy := by
  intro iface
  cases iface with
  | mk thread sealCertType sealCert nameCert ledger =>
      constructor
      · exact Nonempty.intro thread
      · constructor
        · exact Nonempty.intro nameCert
        · exact ledger

omit N in
theorem limit_like_interfaces_derived [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name -> Nonempty (NameCert name) /\ Nonempty LedgerPolicy := by
  intro iface
  cases iface with
  | mk thread sealCertType sealCert nameCert ledger =>
      constructor
      · exact Nonempty.intro nameCert
      · exact ledger

omit N in
theorem sealInterface_certificate_witnesses [NameCertSetup] {Thread : Type} {name : DerivedName}
    (iface : SealInterface Thread name) : NameCert name /\ Nonempty LedgerPolicy := by
  cases iface with
  | mk thread sealCertType sealCert nameCert ledger =>
      exact And.intro nameCert ledger

omit N in
theorem sealInterface_requires_nameCert [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name -> NameCert name ∧ Nonempty LedgerPolicy := by
  intro interface
  constructor
  · exact interface.nameCert
  · exact interface.ledger

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
theorem nameCert_ledger_witness_from_cert [NameCertSetup] {name : DerivedName} :
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

omit N in
theorem sealInterface_nameCert_stability_ledger [NameCertSetup] {Thread : Type}
    {name : DerivedName} :
    SealInterface Thread name -> NameCert name /\ Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro iface
  constructor
  · exact iface.nameCert
  · constructor
    · exact derived_interfaces_have_stability iface.nameCert
    · exact iface.ledger

omit N in
theorem thin_seal_interface_shape [NameCertSetup] {Thread : Type} {name : DerivedName} :
    SealInterface Thread name →
      Nonempty Thread ∧ Nonempty (NameCert name) ∧ Nonempty StabilityCert ∧
        Nonempty LedgerPolicy := by
  intro iface
  constructor
  · exact Nonempty.intro iface.thread
  · constructor
    · exact Nonempty.intro iface.nameCert
    · constructor
      · exact derived_interfaces_have_stability iface.nameCert
      · exact iface.ledger

omit N in
theorem nameCert_source_witness_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty SourceSpec := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact Nonempty.intro source

omit N in
theorem nameCert_pattern_witness_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty PatternSpec := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact Nonempty.intro pattern

omit N in
theorem nameCert_classifier_witness_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty ClassifierSpec := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact Nonempty.intro classifier

omit N in
theorem nameCert_classifier_and_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty ClassifierSpec ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      constructor
      · exact Nonempty.intro classifier
      · exact Nonempty.intro ledger

omit N in
theorem nameCert_source_pattern_classifier_witnesses [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec := by
  intro cert
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact And.intro
        (Nonempty.intro source)
        (And.intro
          (Nonempty.intro pattern)
          (Nonempty.intro classifier))

omit N in
theorem nameCert_pattern_and_classifier_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name → Nonempty PatternSpec ∧ Nonempty ClassifierSpec := by
  intro cert
  cases cert with
  | mk _ pattern classifier _ _ =>
      constructor
      · exact Nonempty.intro pattern
      · exact Nonempty.intro classifier

omit N in
theorem nameCert_stability_witness_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty StabilityCert := by
  intro cert
  cases cert with
  | mk _ _ _ stability _ =>
      exact Nonempty.intro stability

omit N in
theorem nameCert_stability_and_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk _ _ _ stability ledger =>
      constructor
      · exact Nonempty.intro stability
      · exact Nonempty.intro ledger

omit N in
theorem nameCert_source_and_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty SourceSpec ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source _ _ _ ledger =>
      constructor
      · exact Nonempty.intro source
      · exact Nonempty.intro ledger

omit N in
theorem nameCert_source_stability_ledger_from_cert [NameCertSetup] {name : DerivedName} :
    NameCert name -> Nonempty SourceSpec ∧ Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro cert
  cases cert with
  | mk source _ _ stability ledger =>
      constructor
      · exact Nonempty.intro source
      · constructor
        · exact Nonempty.intro stability
        · exact Nonempty.intro ledger

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

theorem nameCert_expanded_template [NameCertSetup] {name : DerivedName} :
    Nonempty (NameCert name) ↔
      ∃ _ : SourceSpec,
      ∃ _ : PatternSpec,
      ∃ _ : ClassifierSpec,
      ∃ _ : StabilityCert,
      ∃ _ : LedgerPolicy, True := by
  constructor
  · intro certNonempty
    cases certNonempty with
    | intro cert =>
        cases cert with
        | mk source pattern classifier stability ledger =>
            exact ⟨source, pattern, classifier, stability, ledger, True.intro⟩
  · intro witnesses
    cases witnesses with
    | intro source rest =>
        cases rest with
        | intro pattern rest =>
            cases rest with
            | intro classifier rest =>
                cases rest with
                | intro stability rest =>
                    cases rest with
                    | intro ledger _ =>
                        exact Nonempty.intro (NameCert.mk source pattern classifier stability ledger)

theorem nameCert_from_field_witnesses [NameCertSetup] {name : DerivedName} :
    SourceSpec -> PatternSpec -> ClassifierSpec -> StabilityCert -> LedgerPolicy -> NameCert name := by
  intro source pattern classifier stability ledger
  exact NameCert.mk source pattern classifier stability ledger

theorem nameCert_from_field_nonempty [NameCertSetup] {name : DerivedName} :
    Nonempty SourceSpec → Nonempty PatternSpec → Nonempty ClassifierSpec →
      Nonempty StabilityCert → Nonempty LedgerPolicy → Nonempty (NameCert name) := by
  intro sourceNonempty patternNonempty classifierNonempty stabilityNonempty ledgerNonempty
  cases sourceNonempty with
  | intro source =>
      cases patternNonempty with
      | intro pattern =>
          cases classifierNonempty with
          | intro classifier =>
              cases stabilityNonempty with
              | intro stability =>
                  cases ledgerNonempty with
                  | intro ledger =>
                      exact Nonempty.intro (NameCert.mk source pattern classifier stability ledger)

theorem nameCert_iff_field_witnesses [NameCertSetup] {name : DerivedName} :
    NameCert name ↔
      ∃ source : SourceSpec,
      ∃ pattern : PatternSpec,
      ∃ classifier : ClassifierSpec,
      ∃ stability : StabilityCert,
      ∃ ledger : LedgerPolicy, True := by
  constructor
  · intro cert
    cases cert with
    | mk source pattern classifier stability ledger =>
        exact ⟨source, pattern, classifier, stability, ledger, True.intro⟩
  · intro witnesses
    cases witnesses with
    | intro source rest =>
        cases rest with
        | intro pattern rest =>
            cases rest with
            | intro classifier rest =>
                cases rest with
                | intro stability rest =>
                    cases rest with
                    | intro ledger _ =>
                        exact NameCert.mk source pattern classifier stability ledger

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

theorem nameCert_field_witnesses_iff [NameCertSetup] {name : DerivedName} :
    NameCert name ↔
      Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
        Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  constructor
  · intro cert
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
  · intro witnesses
    cases witnesses with
    | intro sourceNonempty rest =>
        cases rest with
        | intro patternNonempty rest =>
            cases rest with
            | intro classifierNonempty rest =>
                cases rest with
                | intro stabilityNonempty ledgerNonempty =>
                    cases sourceNonempty with
                    | intro source =>
                        cases patternNonempty with
                        | intro pattern =>
                            cases classifierNonempty with
                            | intro classifier =>
                                cases stabilityNonempty with
                                | intro stability =>
                                    cases ledgerNonempty with
                                    | intro ledger =>
                                        exact NameCert.mk source pattern classifier stability ledger

theorem nameCert_all_field_witnesses_from_nonempty [NameCertSetup] {name : DerivedName} :
    Nonempty (NameCert name) ->
      Nonempty SourceSpec ∧ Nonempty PatternSpec ∧ Nonempty ClassifierSpec ∧
        Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  intro certNonempty
  cases certNonempty with
  | intro cert =>
      exact nameCert_field_witnesses cert

theorem nameCert_stability_ledger_from_nonempty [NameCertSetup] {name : DerivedName} :
    Nonempty (NameCert name) -> Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  intro certNonempty
  cases certNonempty with
  | intro cert =>
      cases cert with
      | mk _ _ _ stability ledger =>
          constructor
          · exact Nonempty.intro stability
          · exact Nonempty.intro ledger

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

structure DescentCertificate
    (Source Target : Type)
    (sourceSame : Source -> Source -> Prop)
    (targetSame : Target -> Target -> Prop) : Type where
  map : Source -> Target
  respects : forall {a b : Source}, sourceSame a b -> targetSame (map a) (map b)

theorem descentCertificate_respects
    {Source Target : Type}
    {sourceSame : Source → Source → Prop}
    {targetSame : Target → Target → Prop}
    (cert : DescentCertificate Source Target sourceSame targetSame)
    {a b : Source} :
    sourceSame a b → targetSame (cert.map a) (cert.map b) := by
  intro same
  cases cert with
  | mk map respects =>
      exact respects same

structure StableTransformation
    (Source Target Ledger : Type)
    (sourceSame : Source -> Source -> Prop)
    (targetSame : Target -> Target -> Prop) : Type where
  map : Source -> Target
  respects : ∀ {a b : Source}, sourceSame a b -> targetSame (map a) (map b)
  ledger : Nonempty Ledger

theorem stableTransformation_ledger_witness
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty Ledger := by
  cases cert with
  | mk map respects ledger =>
      exact ledger

theorem StableTransformation_descentCertificate_exists
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) := by
  cases cert with
  | mk map respects ledger =>
      exact Nonempty.intro { map := map, respects := respects }

theorem stableTransformation_descent_certificate_respects
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame)
    {a b : Source} :
    sourceSame a b ->
      exists descent : DescentCertificate Source Target sourceSame targetSame,
        targetSame (descent.map a) (descent.map b) := by
  intro same
  cases cert with
  | mk map respects ledger =>
      exact ⟨{ map := map, respects := respects }, respects same⟩

theorem stableTransformation_descends_to_packages
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame)
    {a b : Source} :
    sourceSame a b -> targetSame (cert.map a) (cert.map b) := by
  intro same
  cases cert with
  | mk map respects ledger =>
      exact respects same

theorem function_like_interfaces_are_derived
    {Source Target Ledger : Type}
    {sourceSame : Source → Source → Prop}
    {targetSame : Target → Target → Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) ∧
      (∀ {a b : Source}, sourceSame a b → targetSame (cert.map a) (cert.map b)) ∧
      Nonempty Ledger := by
  constructor
  · exact StableTransformation_descentCertificate_exists cert
  · constructor
    · intro a b same
      exact stableTransformation_descends_to_packages cert same
    · exact stableTransformation_ledger_witness cert

theorem function_like_interface_seed_is_derived
    {Source Target Ledger : Type}
    {sourceSame : Source → Source → Prop}
    {targetSame : Target → Target → Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) ∧ Nonempty Ledger := by
  constructor
  · exact StableTransformation_descentCertificate_exists cert
  · exact stableTransformation_ledger_witness cert

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

theorem function_like_interfaces_require_descent
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : { map : Source -> Target //
      (forall {a b : Source}, sourceSame a b -> targetSame (map a) (map b)) /\
        Nonempty Ledger })
    {a b : Source} :
    sourceSame a b -> targetSame (cert.val a) (cert.val b) := by
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
