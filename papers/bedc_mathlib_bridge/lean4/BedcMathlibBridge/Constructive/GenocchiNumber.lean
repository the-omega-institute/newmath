import BEDC.Derived.GenocchiNumberUp
import Mathlib.Data.Int.Basic

/-!
Genocchi-number small-window integer readback.

The BEDC side carries Genocchi numbers through the raw Bernoulli relation. This
bridge exposes only checked integral small values against the host `Int`
constructors and stops before mathlib's Bernoulli surface.
-/

namespace BedcMathlibBridge.Constructive.GenocchiNumber

private def mathlibIntProvenanceAnchor : Unit :=
  let _ : _root_.Int.negSucc = _root_.Int.negSucc := rfl
  let _ : forall n : Nat, _root_.Int.ofNat n = _root_.Int.ofNat n :=
    fun _ => rfl
  ()

def readback (n : Nat) : Int :=
  let _ := mathlibIntProvenanceAnchor
  BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue n

theorem readback_apply (n : Nat) :
    readback n =
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue n := by
  rfl

theorem readback_one :
    readback 1 = _root_.Int.ofNat 1 := by
  rfl

theorem readback_two :
    readback 2 = _root_.Int.negSucc 0 := by
  rfl

theorem readback_four :
    readback 4 = _root_.Int.ofNat 1 := by
  rfl

theorem readback_six :
    readback 6 = _root_.Int.negSucc 2 := by
  rfl

theorem readback_eight :
    readback 8 = _root_.Int.ofNat 17 := by
  rfl

theorem mathlibIntAnchor :
    _root_.Int.negSucc = _root_.Int.negSucc := by
  rfl

theorem small_values_int_anchor
    (_anchor : _root_.Int.negSucc = _root_.Int.negSucc := mathlibIntAnchor) :
    BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 1 =
        _root_.Int.ofNat 1 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 2 =
        _root_.Int.negSucc 0 ∧
        BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 4 =
          _root_.Int.ofNat 1 ∧
          BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 6 =
            _root_.Int.negSucc 2 ∧
            BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 8 =
              _root_.Int.ofNat 17 := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩

theorem raw_small_values :
    BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 0 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 1 =
        { num := 1, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 2 =
        { num := -1, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 3 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 4 =
        { num := 1, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 5 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 6 =
        { num := -3, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 7 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 8 =
        { num := 17, denMinusOne := 0 } := by
  exact BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber_small_values

theorem integral_small_values :
    BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 0 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 1 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 2 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 3 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 4 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 5 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 6 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 7 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 8 := by
  exact BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber_integral_small_values

end BedcMathlibBridge.Constructive.GenocchiNumber
