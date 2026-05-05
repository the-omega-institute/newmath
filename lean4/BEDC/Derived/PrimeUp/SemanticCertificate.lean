import BEDC.Derived.PrimeUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem prime_semantic_name_certificate :
    SemanticNameCert NatPrime NatPrime NatPrime
      (fun h k : BHist => NatPrime h ∧ NatPrime k ∧ hsame h k) := by
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro (BHist.e1 (BHist.e1 BHist.Empty)) NatPrime_first_pair.left
      equiv_refl := by
        intro h hPrime
        exact And.intro hPrime (And.intro hPrime (hsame_refl h))
      equiv_symm := by
        intro _h _k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro _h _k _r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro _h _k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.PrimeUp
