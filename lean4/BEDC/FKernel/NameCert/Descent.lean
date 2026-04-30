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

end BEDC.FKernel.NameCert
