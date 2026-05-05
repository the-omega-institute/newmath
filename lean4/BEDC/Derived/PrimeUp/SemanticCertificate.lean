import BEDC.Derived.PrimeUp.NatMulTransport
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NatMul_result_semanticNameCert {d q : BHist}
    (dUnary : UnaryHistory d) (qUnary : UnaryHistory q) :
    SemanticNameCert (NatMul d q) (NatMul d q) (NatMul d q) hsame := by
  exact {
    core := {
      carrier_inhabited := by
        cases NatMul_total dUnary qUnary with
        | intro result data =>
            exact Exists.intro result data.right
      equiv_refl := by
        intro result _mul
        exact hsame_refl result
      equiv_symm := by
        intro _result _result' same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _result _result' same mul
        exact (NatMul_result_hsame_transport mul same).right
    }
    pattern_sound := by
      intro _result mul
      exact mul
    ledger_sound := by
      intro _result mul
      exact mul
  }

theorem NatDivides_semanticNameCert {d : BHist} (dUnary : UnaryHistory d) :
    SemanticNameCert (NatDivides d) (NatDivides d) (NatDivides d) hsame := by
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro BHist.Empty (Iff.mpr NatDivides_empty_right_iff dUnary)
      equiv_refl := by
        intro dividend _divides
        exact hsame_refl dividend
      equiv_symm := by
        intro _dividend _dividend' same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _dividend _dividend' same divides
        exact (NatDivides_dividend_hsame_transport divides same).right
    }
    pattern_sound := by
      intro _dividend divides
      exact divides
    ledger_sound := by
      intro _dividend divides
      exact divides
  }

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
