import BEDC.Derived.RingUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModNUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RingUp

def ModNQuotientCarrier (modulus h : BHist) : Prop :=
  UnaryHistory modulus ∧ RingSingletonCarrier h

def ModNQuotientClassifier (modulus h k : BHist) : Prop :=
  ModNQuotientCarrier modulus h ∧ ModNQuotientCarrier modulus k ∧
    RingSingletonClassifier h k

theorem ModN_nz_quotient_certificate {modulus : BHist} :
    UnaryHistory modulus ->
      SemanticNameCert (ModNQuotientCarrier modulus) (ModNQuotientCarrier modulus)
        (ModNQuotientCarrier modulus) (ModNQuotientClassifier modulus) := by
  intro modulusUnary
  have emptyRingCarrier : RingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyCarrier : ModNQuotientCarrier modulus BHist.Empty :=
    And.intro modulusUnary emptyRingCarrier
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrierH
        exact And.intro carrierH
          (And.intro carrierH
            (And.intro carrierH.right
              (And.intro carrierH.right (hsame_refl h))))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left
            (And.intro classified.right.right.right.left
              (And.intro classified.right.right.left
                (hsame_symm classified.right.right.right.right))))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (And.intro classifiedHK.right.right.left
              (And.intro classifiedKR.right.right.right.left
                (hsame_trans classifiedHK.right.right.right.right
                  classifiedKR.right.right.right.right))))
      carrier_respects_equiv := by
        intro h k classified _carrierH
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

end BEDC.Derived.ModNUp
