import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MorreySpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MorreySpaceUp : Type where
  | mk (X B F I R T H C P N : BHist) : MorreySpaceUp
  deriving DecidableEq

def morreySpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: morreySpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: morreySpaceEncodeBHist h

def morreySpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (morreySpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (morreySpaceDecodeBHist tail)

private theorem MorreySpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, morreySpaceDecodeBHist (morreySpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def morreySpaceFields : MorreySpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MorreySpaceUp.mk X B F I R T H C P N => [X, B, F, I, R, T, H, C, P, N]

def morreySpaceToEventFlow : MorreySpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (morreySpaceFields x).map morreySpaceEncodeBHist

private def morreySpaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => morreySpaceRawAt index rest

def morreySpaceFromEventFlow (flow : EventFlow) : Option MorreySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MorreySpaceUp.mk
      (morreySpaceDecodeBHist (morreySpaceRawAt 0 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 1 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 2 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 3 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 4 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 5 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 6 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 7 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 8 flow))
      (morreySpaceDecodeBHist (morreySpaceRawAt 9 flow)))

private theorem MorreySpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MorreySpaceUp, morreySpaceFromEventFlow (morreySpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B F I R T H C P N =>
      change
        some
          (MorreySpaceUp.mk
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist X))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist B))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist F))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist I))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist R))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist T))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist H))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist C))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist P))
            (morreySpaceDecodeBHist (morreySpaceEncodeBHist N))) =
          some (MorreySpaceUp.mk X B F I R T H C P N)
      rw [MorreySpaceTasteGate_single_carrier_alignment_decode_encode X,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode B,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode F,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode I,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode R,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode T,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode H,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode C,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode P,
        MorreySpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem MorreySpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MorreySpaceUp} :
    morreySpaceToEventFlow x = morreySpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      morreySpaceFromEventFlow (morreySpaceToEventFlow x) =
        morreySpaceFromEventFlow (morreySpaceToEventFlow y) :=
    congrArg morreySpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MorreySpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MorreySpaceTasteGate_single_carrier_alignment_round_trip y)))

instance morreySpaceBHistCarrier : BHistCarrier MorreySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := morreySpaceToEventFlow
  fromEventFlow := morreySpaceFromEventFlow

instance morreySpaceChapterTasteGate : ChapterTasteGate MorreySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change morreySpaceFromEventFlow (morreySpaceToEventFlow x) = some x
    exact MorreySpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MorreySpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MorreySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  morreySpaceChapterTasteGate

theorem MorreySpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, morreySpaceDecodeBHist (morreySpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MorreySpaceUp) ∧ Nonempty (ChapterTasteGate MorreySpaceUp) ∧
        morreySpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MorreySpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨morreySpaceBHistCarrier⟩,
      ⟨morreySpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MorreySpaceUp
