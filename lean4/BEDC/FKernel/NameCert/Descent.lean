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

end BEDC.FKernel.NameCert
