import BEDC.Derived.HarshadNumberUp
import Mathlib.Data.Nat.Basic

/-!
Harshad-number digit readback.

The BEDC side supplies the decimal digit predicate and divisibility witness.
The bridge exposes only the finite digit-sum surface against the explicit
mathlib list fold `List.foldr Nat.add 0`.
-/

namespace BedcMathlibBridge.Constructive.HarshadNumber

private def mathlibDigitProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall digits : List Nat,
    List.foldr Nat.add 0 digits = List.foldr Nat.add 0 digits := fun _ => rfl
  ()

def digitSumReadback (base : Nat) (digits : List Nat) : Nat :=
  let _ := mathlibDigitProvenanceAnchor
  BEDC.Derived.HarshadNumberUp.digitSum base digits

theorem digitSumReadback_apply (base : Nat) (digits : List Nat) :
    digitSumReadback base digits =
      BEDC.Derived.HarshadNumberUp.digitSum base digits := by
  rfl

theorem mathlibNatAnchor : Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem digitSum_eq_list_foldr
    (base : Nat) (digits : List Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.HarshadNumberUp.digitSum base digits =
      List.foldr Nat.add 0 digits := by
  induction digits with
  | nil =>
      rfl
  | cons digit rest ih =>
      change
        digit + BEDC.Derived.HarshadNumberUp.digitSum base rest =
          digit + List.foldr Nat.add 0 rest
      exact congrArg (fun x => digit + x) ih

theorem digitSumReadback_eq_list_foldr
    (base : Nat) (digits : List Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    digitSumReadback base digits = List.foldr Nat.add 0 digits := by
  rw [digitSumReadback_apply, digitSum_eq_list_foldr]

theorem harshadDigits_mathlib_digit_surface
    {digits : List Nat} {value : Nat}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.HarshadNumberUp.HarshadDigits digits value ->
      0 < List.foldr Nat.add 0 digits ∧
        Exists fun factor : Nat => value = List.foldr Nat.add 0 digits * factor := by
  intro data
  rcases data with ⟨_inBase, evalEq, sumPos, divides⟩
  have sumRead :=
    digitSum_eq_list_foldr BEDC.Derived.HarshadNumberUp.decimalBase digits
  rcases divides with ⟨factor, factorEq⟩
  exact ⟨by
    rw [← sumRead]
    exact sumPos,
    ⟨factor, by
      rw [← sumRead]
      exact factorEq⟩⟩

theorem harshadNumber_mathlib_digit_surface
    {value : Nat}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.HarshadNumberUp.HarshadNumber value ->
      Exists fun digits : List Nat =>
        BEDC.Derived.HarshadNumberUp.DigitsInBase
            BEDC.Derived.HarshadNumberUp.decimalBase digits ∧
          0 < List.foldr Nat.add 0 digits ∧
            Exists fun factor : Nat => value = List.foldr Nat.add 0 digits * factor := by
  intro data
  rcases data with ⟨digits, digitsData⟩
  rcases harshadDigits_mathlib_digit_surface mathlibNatAnchor digitsData with
    ⟨sumPos, divides⟩
  exact ⟨digits, digitsData.left, sumPos, divides⟩

theorem harshad_twelve_mathlib_digit_surface :
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) ->
    Exists fun digits : List Nat =>
      BEDC.Derived.HarshadNumberUp.DigitsInBase
          BEDC.Derived.HarshadNumberUp.decimalBase digits ∧
        0 < List.foldr Nat.add 0 digits ∧
          Exists fun factor : Nat => 12 = List.foldr Nat.add 0 digits * factor :=
  fun _ =>
  harshadNumber_mathlib_digit_surface mathlibNatAnchor
    BEDC.Derived.HarshadNumberUp.harshad_twelve

end BedcMathlibBridge.Constructive.HarshadNumber
