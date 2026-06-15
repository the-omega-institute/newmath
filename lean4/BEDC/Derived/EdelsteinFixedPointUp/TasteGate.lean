import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EdelsteinFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EdelsteinFixedPointUp : Type where
  | mk (X K F O C S H R P N : BHist) : EdelsteinFixedPointUp
  deriving DecidableEq

def edelsteinFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: edelsteinFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: edelsteinFixedPointEncodeBHist h

def edelsteinFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (edelsteinFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (edelsteinFixedPointDecodeBHist tail)

private theorem edelsteinFixedPoint_decode_encode_bhist :
    ∀ h : BHist,
      edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def edelsteinFixedPointFields : EdelsteinFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EdelsteinFixedPointUp.mk X K F O C S H R P N => [X, K, F, O, C, S, H, R, P, N]

def edelsteinFixedPointToEventFlow : EdelsteinFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (edelsteinFixedPointFields x).map edelsteinFixedPointEncodeBHist

private def edelsteinFixedPointRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => edelsteinFixedPointRawAt n rest

private def edelsteinFixedPointLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => edelsteinFixedPointLengthEq n rest

def edelsteinFixedPointFromEventFlow : EventFlow → Option EdelsteinFixedPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match edelsteinFixedPointLengthEq 10 flow with
      | true =>
          some
            (EdelsteinFixedPointUp.mk
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 0 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 1 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 2 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 3 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 4 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 5 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 6 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 7 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 8 flow))
              (edelsteinFixedPointDecodeBHist (edelsteinFixedPointRawAt 9 flow)))
      | false => none

private theorem edelsteinFixedPoint_round_trip :
    ∀ x : EdelsteinFixedPointUp,
      edelsteinFixedPointFromEventFlow (edelsteinFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K F O C S H R P N =>
      change
        some
          (EdelsteinFixedPointUp.mk
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist X))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist K))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist F))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist O))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist C))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist S))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist H))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist R))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist P))
            (edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist N))) =
          some (EdelsteinFixedPointUp.mk X K F O C S H R P N)
      rw [edelsteinFixedPoint_decode_encode_bhist X,
        edelsteinFixedPoint_decode_encode_bhist K,
        edelsteinFixedPoint_decode_encode_bhist F,
        edelsteinFixedPoint_decode_encode_bhist O,
        edelsteinFixedPoint_decode_encode_bhist C,
        edelsteinFixedPoint_decode_encode_bhist S,
        edelsteinFixedPoint_decode_encode_bhist H,
        edelsteinFixedPoint_decode_encode_bhist R,
        edelsteinFixedPoint_decode_encode_bhist P,
        edelsteinFixedPoint_decode_encode_bhist N]

private theorem edelsteinFixedPointToEventFlow_injective {x y : EdelsteinFixedPointUp} :
    edelsteinFixedPointToEventFlow x = edelsteinFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      edelsteinFixedPointFromEventFlow (edelsteinFixedPointToEventFlow x) =
        edelsteinFixedPointFromEventFlow (edelsteinFixedPointToEventFlow y) :=
    congrArg edelsteinFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (edelsteinFixedPoint_round_trip x).symm
      (Eq.trans hread (edelsteinFixedPoint_round_trip y)))

instance edelsteinFixedPointBHistCarrier : BHistCarrier EdelsteinFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := edelsteinFixedPointToEventFlow
  fromEventFlow := edelsteinFixedPointFromEventFlow

instance edelsteinFixedPointChapterTasteGate : ChapterTasteGate EdelsteinFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change edelsteinFixedPointFromEventFlow (edelsteinFixedPointToEventFlow x) = some x
    exact edelsteinFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (edelsteinFixedPointToEventFlow_injective heq)

theorem EdelsteinFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, edelsteinFixedPointDecodeBHist (edelsteinFixedPointEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EdelsteinFixedPointUp) ∧
        Nonempty (ChapterTasteGate EdelsteinFixedPointUp) ∧
          edelsteinFixedPointFields
              (EdelsteinFixedPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨edelsteinFixedPoint_decode_encode_bhist,
      ⟨edelsteinFixedPointBHistCarrier⟩,
      ⟨edelsteinFixedPointChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.EdelsteinFixedPointUp
