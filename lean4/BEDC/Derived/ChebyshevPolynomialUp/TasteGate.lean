import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChebyshevPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChebyshevPolynomialUp : Type where
  | mk (d T0 T1 R W Q H C P N : BHist) : ChebyshevPolynomialUp
  deriving DecidableEq

def chebyshevPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: chebyshevPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: chebyshevPolynomialEncodeBHist h

def chebyshevPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (chebyshevPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (chebyshevPolynomialDecodeBHist tail)

private theorem ChebyshevPolynomialTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def chebyshevPolynomialFields : ChebyshevPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChebyshevPolynomialUp.mk d T0 T1 R W Q H C P N => [d, T0, T1, R, W, Q, H, C, P, N]

def chebyshevPolynomialToEventFlow : ChebyshevPolynomialUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (chebyshevPolynomialFields x).map chebyshevPolynomialEncodeBHist

private def chebyshevPolynomialEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => chebyshevPolynomialEventAtDefault index rest

def chebyshevPolynomialFromEventFlow
    (ef : EventFlow) : Option ChebyshevPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ChebyshevPolynomialUp.mk
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 0 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 1 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 2 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 3 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 4 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 5 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 6 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 7 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 8 ef))
      (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEventAtDefault 9 ef)))

private theorem ChebyshevPolynomialTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChebyshevPolynomialUp,
      chebyshevPolynomialFromEventFlow
          (chebyshevPolynomialToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk d T0 T1 R W Q H C P N =>
      change
        some
          (ChebyshevPolynomialUp.mk
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist d))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist T0))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist T1))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist R))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist W))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist Q))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist H))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist C))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist P))
            (chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist N))) =
          some (ChebyshevPolynomialUp.mk d T0 T1 R W Q H C P N)
      rw [ChebyshevPolynomialTasteGate_single_carrier_alignment_decode d,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode T0,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode T1,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode R,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode W,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode Q,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode H,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode C,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode P,
        ChebyshevPolynomialTasteGate_single_carrier_alignment_decode N]

private theorem ChebyshevPolynomialTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ChebyshevPolynomialUp} :
    chebyshevPolynomialToEventFlow x = chebyshevPolynomialToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      chebyshevPolynomialFromEventFlow (chebyshevPolynomialToEventFlow x) =
        chebyshevPolynomialFromEventFlow (chebyshevPolynomialToEventFlow y) :=
    congrArg chebyshevPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ChebyshevPolynomialTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ChebyshevPolynomialTasteGate_single_carrier_alignment_round_trip y)))

instance chebyshevPolynomialBHistCarrier : BHistCarrier ChebyshevPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := chebyshevPolynomialToEventFlow
  fromEventFlow := chebyshevPolynomialFromEventFlow

instance chebyshevPolynomialChapterTasteGate : ChapterTasteGate ChebyshevPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change chebyshevPolynomialFromEventFlow (chebyshevPolynomialToEventFlow x) = some x
    exact ChebyshevPolynomialTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ChebyshevPolynomialTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ChebyshevPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  chebyshevPolynomialChapterTasteGate

theorem ChebyshevPolynomialTasteGate_single_carrier_alignment :
    (∀ h : BHist, chebyshevPolynomialDecodeBHist (chebyshevPolynomialEncodeBHist h) = h) ∧
      (∀ x : ChebyshevPolynomialUp,
        chebyshevPolynomialFromEventFlow (chebyshevPolynomialToEventFlow x) = some x) ∧
        (∀ x y : ChebyshevPolynomialUp,
          chebyshevPolynomialToEventFlow x = chebyshevPolynomialToEventFlow y → x = y) ∧
          chebyshevPolynomialEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ChebyshevPolynomialTasteGate_single_carrier_alignment_decode,
      ChebyshevPolynomialTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ChebyshevPolynomialTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ChebyshevPolynomialUp
