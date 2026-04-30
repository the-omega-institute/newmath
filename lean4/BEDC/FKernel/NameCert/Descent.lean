import BEDC.FKernel.NameCert

namespace BEDC.FKernel.NameCert

theorem stableTransformation_descent_and_ledger
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) ∧ Nonempty Ledger := by
  cases cert with
  | mk map respects ledger =>
      constructor
      · exact Nonempty.intro { map := map, respects := respects }
      · exact ledger

theorem StableTransformation_descentCertificate_respects_projection
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    exists descent : DescentCertificate Source Target sourceSame targetSame,
      forall {a b : Source}, sourceSame a b -> targetSame (descent.map a) (descent.map b) := by
  cases cert with
  | mk map respects ledger =>
      exact ⟨{ map := map, respects := respects }, fun {a b} same => respects same⟩

theorem function_like_interface_seed_not_primitive
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) /\ Nonempty Ledger := by
  have derived := function_like_interface_seed_is_derived cert
  constructor
  · exact derived.left
  · exact derived.right

theorem stableTransformation_descent_respects_and_ledger
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame)
    {a b : Source} :
    sourceSame a b ->
      exists descent : DescentCertificate Source Target sourceSame targetSame,
        targetSame (descent.map a) (descent.map b) /\ Nonempty Ledger := by
  intro same
  cases cert with
  | mk map respects ledger =>
      exact Exists.intro { map := map, respects := respects }
        (And.intro (respects same) ledger)

theorem stableTransformation_respects_and_ledger
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame)
    {a b : Source} :
    sourceSame a b -> targetSame (cert.map a) (cert.map b) ∧ Nonempty Ledger := by
  intro same
  constructor
  · exact stableTransformation_descends_to_packages cert same
  · exact stableTransformation_ledger_witness cert

theorem stableTransformation_respects_with_descent_certificate
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame)
    {a b : Source} :
    sourceSame a b ->
      exists descent : DescentCertificate Source Target sourceSame targetSame,
        targetSame (descent.map a) (descent.map b) ∧
          targetSame (cert.map a) (cert.map b) ∧ Nonempty Ledger := by
  intro same
  cases cert with
  | mk map respects ledger =>
      exact Exists.intro { map := map, respects := respects }
        (And.intro (respects same)
          (And.intro (respects same) ledger))

theorem StableTransformation_descent_respects_ledger_pair
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame)
    {a b : Source} :
    sourceSame a b ->
      targetSame (cert.map a) (cert.map b) /\
        Nonempty (DescentCertificate Source Target sourceSame targetSame) /\ Nonempty Ledger := by
  intro same
  cases cert with
  | mk map respects ledger =>
      exact And.intro (respects same)
        (And.intro (Nonempty.intro { map := map, respects := respects }) ledger)

theorem function_like_interfaces_derived_core
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) ∧
      (∀ {a b : Source}, sourceSame a b -> targetSame (cert.map a) (cert.map b)) ∧
      Nonempty Ledger := by
  constructor
  · exact StableTransformation_descentCertificate_exists cert
  · constructor
    · intro a b same
      exact stableTransformation_descends_to_packages cert same
    · exact stableTransformation_ledger_witness cert

theorem StableTransformation_descent_certificate_and_respects
    {Source Target Ledger : Type}
    {sourceSame : Source -> Source -> Prop}
    {targetSame : Target -> Target -> Prop}
    (cert : StableTransformation Source Target Ledger sourceSame targetSame) :
    Nonempty (DescentCertificate Source Target sourceSame targetSame) ∧
      (∀ {a b : Source}, sourceSame a b → targetSame (cert.map a) (cert.map b)) := by
  cases cert with
  | mk map respects ledger =>
      constructor
      · exact Nonempty.intro { map := map, respects := respects }
      · intro a b same
        exact respects same

theorem descentCertificate_respects_witness
    {Source Target : Type}
    {sourceSame : Source → Source → Prop}
    {targetSame : Target → Target → Prop}
    (cert : DescentCertificate Source Target sourceSame targetSame)
    {a b : Source} :
    sourceSame a b →
      ∃ map : Source → Target, map = cert.map ∧ targetSame (map a) (map b) := by
  intro same
  exact Exists.intro cert.map (And.intro rfl (descentCertificate_respects cert same))

theorem descentCertificate_respects_pair_with_map
    {Source Target : Type}
    {sourceSame : Source → Source → Prop}
    {targetSame : Target → Target → Prop}
    (cert : DescentCertificate Source Target sourceSame targetSame)
    {a b : Source} :
    sourceSame a b →
      targetSame (cert.map a) (cert.map b) ∧ ∃ map : Source → Target, map = cert.map := by
  intro same
  constructor
  · exact descentCertificate_respects cert same
  · exact Exists.intro cert.map rfl

end BEDC.FKernel.NameCert
