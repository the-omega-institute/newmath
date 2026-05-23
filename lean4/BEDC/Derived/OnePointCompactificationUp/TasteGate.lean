import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnePointCompactificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnePointCompactificationUp : Type where
  | mk (X L B infinity Q T K H C P N : BHist) : OnePointCompactificationUp
  deriving DecidableEq

def onePointCompactificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onePointCompactificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onePointCompactificationEncodeBHist h

def onePointCompactificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onePointCompactificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onePointCompactificationDecodeBHist tail)

private theorem OnePointCompactificationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      onePointCompactificationDecodeBHist (onePointCompactificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def onePointCompactificationFields : OnePointCompactificationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnePointCompactificationUp.mk X L B infinity Q T K H C P N =>
      [X, L, B, infinity, Q, T, K, H, C, P, N]

def onePointCompactificationToEventFlow : OnePointCompactificationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (onePointCompactificationFields x).map onePointCompactificationEncodeBHist

private def onePointCompactificationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => onePointCompactificationEventAtDefault index rest

def onePointCompactificationFromEventFlow
    (ef : EventFlow) : Option OnePointCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OnePointCompactificationUp.mk
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 0 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 1 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 2 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 3 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 4 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 5 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 6 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 7 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 8 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 9 ef))
      (onePointCompactificationDecodeBHist
        (onePointCompactificationEventAtDefault 10 ef)))

private theorem OnePointCompactificationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OnePointCompactificationUp,
      onePointCompactificationFromEventFlow
          (onePointCompactificationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X L B infinity Q T K H C P N =>
      change
        some
          (OnePointCompactificationUp.mk
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist X))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist L))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist B))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist infinity))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist Q))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist T))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist K))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist H))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist C))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist P))
            (onePointCompactificationDecodeBHist
              (onePointCompactificationEncodeBHist N))) =
          some (OnePointCompactificationUp.mk X L B infinity Q T K H C P N)
      rw [OnePointCompactificationTasteGate_single_carrier_alignment_decode X,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode L,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode B,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode infinity,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode Q,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode T,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode K,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode H,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode C,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode P,
        OnePointCompactificationTasteGate_single_carrier_alignment_decode N]

private theorem OnePointCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OnePointCompactificationUp} :
    onePointCompactificationToEventFlow x = onePointCompactificationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onePointCompactificationFromEventFlow (onePointCompactificationToEventFlow x) =
        onePointCompactificationFromEventFlow (onePointCompactificationToEventFlow y) :=
    congrArg onePointCompactificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OnePointCompactificationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OnePointCompactificationTasteGate_single_carrier_alignment_round_trip y)))

instance onePointCompactificationBHistCarrier :
    BHistCarrier OnePointCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onePointCompactificationToEventFlow
  fromEventFlow := onePointCompactificationFromEventFlow

instance onePointCompactificationChapterTasteGate :
    ChapterTasteGate OnePointCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      onePointCompactificationFromEventFlow (onePointCompactificationToEventFlow x) =
        some x
    exact OnePointCompactificationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (OnePointCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate OnePointCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  onePointCompactificationChapterTasteGate

theorem OnePointCompactificationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      onePointCompactificationDecodeBHist (onePointCompactificationEncodeBHist h) = h) ∧
      (∀ x : OnePointCompactificationUp,
        onePointCompactificationFromEventFlow (onePointCompactificationToEventFlow x) =
          some x) ∧
        (∀ x y : OnePointCompactificationUp,
          onePointCompactificationToEventFlow x =
            onePointCompactificationToEventFlow y → x = y) ∧
          onePointCompactificationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨OnePointCompactificationTasteGate_single_carrier_alignment_decode,
      OnePointCompactificationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        OnePointCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.OnePointCompactificationUp
