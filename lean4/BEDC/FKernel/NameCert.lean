import BEDC.FKernel.Gap

/-! Semantic naming certificates over BEDC histories. -/
namespace BEDC.FKernel.NameCert

open BEDC.FKernel.Hist

inductive StageInterface where
  | base : StageInterface

def ThreadFamily (StageData : StageInterface -> Type) : Type :=
  (stage : StageInterface) -> StageData stage

structure NameCert
    (Carrier : BHist -> Prop)
    (Equiv : BHist -> BHist -> Prop) : Prop where
  carrier_inhabited : exists h : BHist, Carrier h
  equiv_refl : forall {h : BHist}, Carrier h -> Equiv h h
  equiv_symm : forall {h k : BHist}, Equiv h k -> Equiv k h
  equiv_trans : forall {h k r : BHist}, Equiv h k -> Equiv k r -> Equiv h r
  carrier_respects_equiv : forall {h k : BHist}, Equiv h k -> Carrier h -> Carrier k

structure SemanticNameCert
    (SourceSpec PatternSpec LedgerPolicy : BHist -> Prop)
    (ClassifierSpec : BHist -> BHist -> Prop) : Prop where
  core : NameCert SourceSpec ClassifierSpec
  pattern_sound : forall {h : BHist}, SourceSpec h -> PatternSpec h
  ledger_sound : forall {h : BHist}, SourceSpec h -> LedgerPolicy h

theorem semanticNameCert_ledger_policy_witness
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec) :
    exists h : BHist, LedgerPolicy h := by
  cases cert with
  | mk core _ ledger_sound =>
      cases core with
      | mk carrier_inhabited _ _ _ _ =>
          cases carrier_inhabited with
          | intro h source =>
              exact Exists.intro h (ledger_sound source)

theorem semanticNameCert_pattern_ledger_witness
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec) :
    exists h : BHist, PatternSpec h /\ LedgerPolicy h := by
  have core : NameCert SourceSpec ClassifierSpec := cert.core
  have pattern_sound : forall {h : BHist}, SourceSpec h -> PatternSpec h :=
    cert.pattern_sound
  have ledger_sound : forall {h : BHist}, SourceSpec h -> LedgerPolicy h :=
    cert.ledger_sound
  cases core with
  | mk carrier_inhabited _ _ _ _ =>
      cases carrier_inhabited with
          | intro h source =>
              exact Exists.intro h (And.intro (pattern_sound source) (ledger_sound source))

theorem semanticNameCert_pattern_ledger_transport
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec)
    {h k : BHist} :
    ClassifierSpec h k -> SourceSpec h -> PatternSpec k ∧ LedgerPolicy k := by
  intro classified sourceH
  have sourceK : SourceSpec k :=
    BEDC.FKernel.NameCert.NameCert.carrier_respects_equiv cert.core classified sourceH
  exact And.intro (cert.pattern_sound sourceK) (cert.ledger_sound sourceK)

theorem NameCert_iff_semantic_fields
    {Carrier : BHist -> Prop}
    {Equiv : BHist -> BHist -> Prop} :
    NameCert Carrier Equiv <->
      (exists h : BHist, Carrier h) /\
        (forall {h : BHist}, Carrier h -> Equiv h h) /\
        (forall {h k : BHist}, Equiv h k -> Equiv k h) /\
        (forall {h k r : BHist}, Equiv h k -> Equiv k r -> Equiv h r) /\
        (forall {h k : BHist}, Equiv h k -> Carrier h -> Carrier k) := by
  constructor
  · intro cert
    cases cert with
    | mk carrier_inhabited equiv_refl equiv_symm equiv_trans carrier_respects_equiv =>
        constructor
        · exact carrier_inhabited
        · constructor
          · exact equiv_refl
          · constructor
            · exact equiv_symm
            · constructor
              · exact equiv_trans
              · exact carrier_respects_equiv
  · intro fields
    cases fields with
    | intro carrier_inhabited rest =>
        cases rest with
        | intro equiv_refl rest =>
            cases rest with
            | intro equiv_symm rest =>
                cases rest with
                | intro equiv_trans carrier_respects_equiv =>
                    exact {
                      carrier_inhabited := carrier_inhabited
                      equiv_refl := equiv_refl
                      equiv_symm := equiv_symm
                      equiv_trans := equiv_trans
                      carrier_respects_equiv := carrier_respects_equiv
                    }

theorem nameCert_carrier_witness
    {Carrier : BHist -> Prop}
    {Equiv : BHist -> BHist -> Prop}
    (cert : NameCert Carrier Equiv) :
    exists h : BHist, Carrier h := by
  cases cert with
  | mk carrier_inhabited _ _ _ _ =>
      exact carrier_inhabited

theorem nameCert_equiv_refl
    {Carrier : BHist -> Prop}
    {Equiv : BHist -> BHist -> Prop}
    (cert : NameCert Carrier Equiv)
    {h : BHist} :
    Carrier h -> Equiv h h := by
  intro carrier
  cases cert with
  | mk _ equiv_refl _ _ _ =>
      exact equiv_refl carrier

theorem nameCert_equiv_trans
    {Carrier : BEDC.FKernel.Hist.BHist -> Prop}
    {Equiv : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop}
    (cert : BEDC.FKernel.NameCert.NameCert Carrier Equiv)
    {h k r : BEDC.FKernel.Hist.BHist} :
    Equiv h k -> Equiv k r -> Equiv h r := by
  intro sameHK sameKR
  exact BEDC.FKernel.NameCert.NameCert.equiv_trans cert sameHK sameKR

theorem nameCert_carrier_transport
    {Carrier : BHist -> Prop}
    {Equiv : BHist -> BHist -> Prop}
    (cert : NameCert Carrier Equiv)
    {h k : BHist} :
    Equiv h k -> Carrier h -> Carrier k := by
  intro same carrier
  cases cert with
  | mk _ _ _ _ carrier_respects_equiv =>
      exact carrier_respects_equiv same carrier

theorem derived_interfaces_require_certificates
    {Carrier : BHist -> Prop}
    {Equiv : BHist -> BHist -> Prop}
    (cert : NameCert Carrier Equiv) :
    (∃ h : BHist, Carrier h) ∧
      (∀ {h : BHist}, Carrier h -> Equiv h h) ∧
      (∀ {h k : BHist}, Equiv h k -> Equiv k h) ∧
      (∀ {h k r : BHist}, Equiv h k -> Equiv k r -> Equiv h r) ∧
      (∀ {h k : BHist}, Equiv h k -> Carrier h -> Carrier k) := by
  have certData : BEDC.FKernel.NameCert.NameCert Carrier Equiv := cert
  cases certData with
  | mk carrier_inhabited equiv_refl equiv_symm equiv_trans carrier_respects_equiv =>
      constructor
      · exact carrier_inhabited
      · constructor
        · intro h carrier
          exact equiv_refl carrier
        · constructor
          · intro h k same
            exact equiv_symm same
          · constructor
            · intro h k r same_hk same_kr
              exact equiv_trans same_hk same_kr
            · intro h k same carrier
              exact carrier_respects_equiv same carrier

structure SealEvent
    (Carrier : BHist -> Prop)
    (Equiv : BHist -> BHist -> Prop) : Prop where
  nameCert : NameCert Carrier Equiv

structure SealInterface
    (Thread : Type)
    (Carrier : BHist -> Prop)
    (Equiv : BHist -> BHist -> Prop) : Type 1 where
  thread : Thread
  nameCert : NameCert Carrier Equiv

theorem sealInterface_thread_witness
    {Thread : Type}
    {Carrier : BHist -> Prop}
    {Equiv : BHist -> BHist -> Prop} :
    SealInterface Thread Carrier Equiv -> Nonempty Thread := by
  intro iface
  exact Nonempty.intro iface.thread

theorem sealInterface_certificate_witness
    {Thread : Type}
    {Carrier : BHist -> Prop}
    {Equiv : BHist -> BHist -> Prop} :
    SealInterface Thread Carrier Equiv -> Nonempty (NameCert Carrier Equiv) := by
  intro iface
  exact Nonempty.intro iface.nameCert

structure DescentCertificate
    (Source Target : Type)
    (sourceSame : Source -> Source -> Prop)
    (targetSame : Target -> Target -> Prop) : Type where
  map : Source -> Target
  respects : forall {a b : Source}, sourceSame a b -> targetSame (map a) (map b)

theorem descentCertificate_respects
    {Source Target : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : DescentCertificate Source Target sourceSame targetSame)
    {a b : Source} :
    sourceSame a b -> targetSame (cert.map a) (cert.map b) := by
  intro same
  cases cert with
  | mk map respects =>
      exact respects same

structure StableTransformation
    (Source Target Ledger : Type)
    (sourceSame : Source -> Source -> Prop)
    (targetSame : Target -> Target -> Prop) : Type where
  map : Source -> Target
  respects : forall {a b : Source}, sourceSame a b -> targetSame (map a) (map b)
  ledger : Nonempty Ledger

theorem stableTransformation_ledger_witness
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty Ledger := by
  cases cert with
  | mk _ _ ledger =>
      exact ledger

theorem StableTransformation_descentCertificate_exists
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) := by
  cases cert with
  | mk map respects _ =>
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
  | mk map respects _ =>
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
  | mk _ respects _ =>
      exact respects same

theorem function_like_interfaces_are_derived
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) ∧
      (forall {a b : Source}, sourceSame a b -> targetSame (cert.map a) (cert.map b)) ∧
      Nonempty Ledger := by
  constructor
  · exact StableTransformation_descentCertificate_exists cert
  · constructor
    · intro a b same
      exact stableTransformation_descends_to_packages cert same
    · exact stableTransformation_ledger_witness cert

theorem function_like_interface_seed_is_derived
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) ∧ Nonempty Ledger := by
  constructor
  · exact StableTransformation_descentCertificate_exists cert
  · exact stableTransformation_ledger_witness cert

theorem stable_transform_descends_to_packages
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert :
      { map : Source -> Target //
        (forall {a b : Source}, sourceSame a b -> targetSame (map a) (map b)) ∧
          Nonempty Ledger })
    {a b : Source} :
    sourceSame a b -> targetSame (cert.val a) (cert.val b) := by
  intro same
  cases cert with
  | mk _ certData =>
      exact certData.left same

theorem function_like_interfaces_require_descent
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert :
      { map : Source -> Target //
        (forall {a b : Source}, sourceSame a b -> targetSame (map a) (map b)) ∧
          Nonempty Ledger })
    {a b : Source} :
    sourceSame a b -> targetSame (cert.val a) (cert.val b) := by
  intro same
  exact stable_transform_descends_to_packages cert same

end BEDC.FKernel.NameCert
