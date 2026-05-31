import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RatioCauchyTransferUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RatioCauchyTransferUp : Type where
  | mk (N D A R Q H C P L : BHist) : RatioCauchyTransferUp
  deriving DecidableEq

def ratioCauchyTransferEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ratioCauchyTransferEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ratioCauchyTransferEncodeBHist h

def ratioCauchyTransferDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ratioCauchyTransferDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ratioCauchyTransferDecodeBHist tail)

private theorem ratioCauchyTransfer_decode_encode_bhist :
    ∀ h : BHist, ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def ratioCauchyTransferFields : RatioCauchyTransferUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RatioCauchyTransferUp.mk N D A R Q H C P L => [N, D, A, R, Q, H, C, P, L]

def ratioCauchyTransferToEventFlow : RatioCauchyTransferUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ratioCauchyTransferFields x).map ratioCauchyTransferEncodeBHist

private def ratioCauchyTransferRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ratioCauchyTransferRawAt index rest

private def ratioCauchyTransferLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => ratioCauchyTransferLengthEq index rest

def ratioCauchyTransferFromEventFlow : EventFlow → Option RatioCauchyTransferUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match ratioCauchyTransferLengthEq 9 flow with
      | true =>
          some
            (RatioCauchyTransferUp.mk
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 0 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 1 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 2 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 3 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 4 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 5 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 6 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 7 flow))
              (ratioCauchyTransferDecodeBHist (ratioCauchyTransferRawAt 8 flow)))
      | false => none

private theorem ratioCauchyTransfer_round_trip :
    ∀ x : RatioCauchyTransferUp,
      ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N D A R Q H C P L =>
      change
        some
          (RatioCauchyTransferUp.mk
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist N))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist D))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist A))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist R))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist Q))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist H))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist C))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist P))
            (ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist L))) =
          some (RatioCauchyTransferUp.mk N D A R Q H C P L)
      rw [ratioCauchyTransfer_decode_encode_bhist N,
        ratioCauchyTransfer_decode_encode_bhist D,
        ratioCauchyTransfer_decode_encode_bhist A,
        ratioCauchyTransfer_decode_encode_bhist R,
        ratioCauchyTransfer_decode_encode_bhist Q,
        ratioCauchyTransfer_decode_encode_bhist H,
        ratioCauchyTransfer_decode_encode_bhist C,
        ratioCauchyTransfer_decode_encode_bhist P,
        ratioCauchyTransfer_decode_encode_bhist L]

private theorem ratioCauchyTransferToEventFlow_injective {x y : RatioCauchyTransferUp} :
    ratioCauchyTransferToEventFlow x = ratioCauchyTransferToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) =
        ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow y) :=
    congrArg ratioCauchyTransferFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ratioCauchyTransfer_round_trip x).symm
      (Eq.trans hread (ratioCauchyTransfer_round_trip y)))

instance ratioCauchyTransferBHistCarrier : BHistCarrier RatioCauchyTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ratioCauchyTransferToEventFlow
  fromEventFlow := ratioCauchyTransferFromEventFlow

instance ratioCauchyTransferChapterTasteGate : ChapterTasteGate RatioCauchyTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) = some x
    exact ratioCauchyTransfer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ratioCauchyTransferToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RatioCauchyTransferUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ratioCauchyTransferChapterTasteGate

theorem RatioCauchyTransferTasteGate_single_carrier_alignment :
    (∀ h : BHist, ratioCauchyTransferDecodeBHist (ratioCauchyTransferEncodeBHist h) = h) ∧
      (∀ x : RatioCauchyTransferUp,
        ratioCauchyTransferFromEventFlow (ratioCauchyTransferToEventFlow x) = some x) ∧
      (∀ x y : RatioCauchyTransferUp,
        ratioCauchyTransferToEventFlow x = ratioCauchyTransferToEventFlow y → x = y) ∧
      ratioCauchyTransferEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ratioCauchyTransfer_decode_encode_bhist,
      ratioCauchyTransfer_round_trip,
      (fun _ _ heq => ratioCauchyTransferToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RatioCauchyTransferUp
