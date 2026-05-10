import BEDC.Derived.PrimeUp.SemanticCertificate
import BEDC.Derived.PrimeUp.PrimeShape

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem PrimeUp_StdBridge :
    SemanticNameCert NatPrime NatPrime NatPrime
        (fun h k : BHist => NatPrime h ∧ NatPrime k ∧ hsame h k) ∧
      (forall {p p' : BHist}, NatPrime p -> hsame p p' -> UnaryHistory p' ∧ NatPrime p') ∧
      NatPrime (BHist.e1 (BHist.e1 BHist.Empty)) ∧
      (fun h k : BHist => NatPrime h ∧ NatPrime k ∧ hsame h k)
        (BHist.e1 (BHist.e1 BHist.Empty)) (BHist.e1 (BHist.e1 BHist.Empty)) := by
  constructor
  · exact prime_semantic_name_certificate
  · constructor
    · exact PrimeStabilityCert_fields.left
    · constructor
      · exact NatPrime_first_pair.left
      · exact And.intro NatPrime_first_pair.left
          (And.intro NatPrime_first_pair.left (hsame_refl _))

end BEDC.Derived.PrimeUp
