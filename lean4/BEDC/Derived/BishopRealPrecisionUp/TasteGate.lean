import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealPrecisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealPrecisionUp : Type where
  | mk (D W R E M H C Q N : BHist) : BishopRealPrecisionUp
  deriving DecidableEq

def bishopRealPrecisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealPrecisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealPrecisionEncodeBHist h

def bishopRealPrecisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealPrecisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealPrecisionDecodeBHist tail)

private theorem BishopRealPrecisionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealPrecisionFields : BishopRealPrecisionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealPrecisionUp.mk D W R E M H C Q N => [D, W, R, E, M, H, C, Q, N]

def bishopRealPrecisionToEventFlow : BishopRealPrecisionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopRealPrecisionFields x).map bishopRealPrecisionEncodeBHist

private def bishopRealPrecisionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealPrecisionRawAt index rest

def bishopRealPrecisionFromEventFlow (flow : EventFlow) : Option BishopRealPrecisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRealPrecisionUp.mk
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 0 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 1 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 2 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 3 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 4 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 5 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 6 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 7 flow))
      (bishopRealPrecisionDecodeBHist (bishopRealPrecisionRawAt 8 flow)))

private theorem BishopRealPrecisionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRealPrecisionUp,
      bishopRealPrecisionFromEventFlow (bishopRealPrecisionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk D W R E M H C Q N =>
      change
        some
          (BishopRealPrecisionUp.mk
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist D))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist W))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist R))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist E))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist M))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist H))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist C))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist Q))
            (bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist N))) =
          some (BishopRealPrecisionUp.mk D W R E M H C Q N)
      rw [BishopRealPrecisionTasteGate_single_carrier_alignment_decode D,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode W,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode R,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode E,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode M,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode H,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode C,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode Q,
        BishopRealPrecisionTasteGate_single_carrier_alignment_decode N]

private theorem bishopRealPrecisionToEventFlow_injective {x y : BishopRealPrecisionUp} :
    bishopRealPrecisionToEventFlow x = bishopRealPrecisionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealPrecisionFromEventFlow (bishopRealPrecisionToEventFlow x) =
        bishopRealPrecisionFromEventFlow (bishopRealPrecisionToEventFlow y) :=
    congrArg bishopRealPrecisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealPrecisionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopRealPrecisionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRealPrecisionBHistCarrier : BHistCarrier BishopRealPrecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealPrecisionToEventFlow
  fromEventFlow := bishopRealPrecisionFromEventFlow

instance bishopRealPrecisionChapterTasteGate : ChapterTasteGate BishopRealPrecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealPrecisionFromEventFlow (bishopRealPrecisionToEventFlow x) = some x
    exact BishopRealPrecisionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRealPrecisionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopRealPrecisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRealPrecisionChapterTasteGate

theorem BishopRealPrecisionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRealPrecisionDecodeBHist (bishopRealPrecisionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopRealPrecisionUp) ∧
        Nonempty (ChapterTasteGate BishopRealPrecisionUp) ∧
          bishopRealPrecisionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRealPrecisionTasteGate_single_carrier_alignment_decode,
      ⟨bishopRealPrecisionBHistCarrier⟩,
      ⟨bishopRealPrecisionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopRealPrecisionUp
