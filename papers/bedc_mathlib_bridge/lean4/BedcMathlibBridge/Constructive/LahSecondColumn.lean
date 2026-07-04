import BedcMathlibBridge.Constructive.Binomial
import BedcMathlibBridge.Constructive.LahClosedForm
import BEDC.Derived.LahNumberUp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
Lah second-column closed numerator and denominator surface.

The BEDC side already exposes the Lah closed-form numerator and denominator.
This bridge exports the second nonzero column surface against the corresponding
`Nat.choose` and `Nat.factorial` expression, without claiming the full quotient
or a host-named Lah-number API.
-/

namespace BedcMathlibBridge.Constructive.LahSecondColumn

private def mathlibChooseFactorialProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

private theorem C_eq_nat_choose (n k : Nat) :
    BEDC.Derived.LahNumberUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

def secondColumnReadback (n : Nat) : Nat :=
  let _ := mathlibChooseFactorialProvenanceAnchor
  BEDC.Derived.LahNumberUp.lahNumber (Nat.succ (Nat.succ n)) 2

def secondColumnClosedNumeratorReadback (n : Nat) : Nat :=
  let _ := mathlibChooseFactorialProvenanceAnchor
  BEDC.Derived.LahNumberUp.lahClosedNumerator (Nat.succ (Nat.succ n)) 2

def secondColumnClosedDenominatorReadback : Nat :=
  let _ := mathlibChooseFactorialProvenanceAnchor
  BEDC.Derived.LahNumberUp.lahClosedDenominator 2

def mathlibSecondColumnNumerator (n : Nat) : Nat :=
  Nat.choose (Nat.succ n) 1 * Nat.factorial (Nat.succ (Nat.succ n))

def mathlibSecondColumnDenominator : Nat :=
  Nat.factorial 2

theorem secondColumnReadback_apply (n : Nat) :
    secondColumnReadback n =
      BEDC.Derived.LahNumberUp.lahNumber (Nat.succ (Nat.succ n)) 2 := by
  rfl

theorem secondColumnClosedNumerator_apply (n : Nat) :
    secondColumnClosedNumeratorReadback n =
      BEDC.Derived.LahNumberUp.lahClosedNumerator
        (Nat.succ (Nat.succ n)) 2 := by
  rfl

theorem secondColumnClosedDenominator_apply :
    secondColumnClosedDenominatorReadback =
      BEDC.Derived.LahNumberUp.lahClosedDenominator 2 := by
  rfl

theorem secondColumnClosedNumerator_eq_mathlib (n : Nat) :
    secondColumnClosedNumeratorReadback n =
      mathlibSecondColumnNumerator n := by
  unfold secondColumnClosedNumeratorReadback mathlibSecondColumnNumerator
  unfold BEDC.Derived.LahNumberUp.lahClosedNumerator
  change
    BEDC.Derived.LahNumberUp.C (Nat.succ n) 1 *
        BEDC.Derived.LahNumberUp.factorialNat (Nat.succ (Nat.succ n)) =
      Nat.choose (Nat.succ n) 1 * Nat.factorial (Nat.succ (Nat.succ n))
  rw [C_eq_nat_choose (Nat.succ n) 1]
  rw [BedcMathlibBridge.Constructive.LahClosedForm.factorialNat_eq_nat_factorial]

theorem secondColumnClosedDenominator_eq_mathlib :
    secondColumnClosedDenominatorReadback =
      mathlibSecondColumnDenominator := by
  unfold secondColumnClosedDenominatorReadback mathlibSecondColumnDenominator
  unfold BEDC.Derived.LahNumberUp.lahClosedDenominator
  exact
    BedcMathlibBridge.Constructive.LahClosedForm.factorialNat_eq_nat_factorial 2

theorem secondColumnClosedNumerator_eq_nat_choose_factorial (n : Nat) :
    BEDC.Derived.LahNumberUp.lahClosedNumerator
        (Nat.succ (Nat.succ n)) 2 =
      Nat.choose (Nat.succ n) 1 * Nat.factorial (Nat.succ (Nat.succ n)) := by
  exact
    (secondColumnClosedNumerator_apply n).symm.trans
      (secondColumnClosedNumerator_eq_mathlib n)

end BedcMathlibBridge.Constructive.LahSecondColumn
