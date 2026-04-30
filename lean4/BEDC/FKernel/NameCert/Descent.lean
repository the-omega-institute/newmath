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

end BEDC.FKernel.NameCert
