import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MorseBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MorseBoundaryUp : Type where
  | mk (X G S F B H C P N : BHist) : MorseBoundaryUp
  deriving DecidableEq

def morseBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: morseBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: morseBoundaryEncodeBHist h

def morseBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (morseBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (morseBoundaryDecodeBHist tail)

private theorem morseBoundary_decode_encode_bhist :
    ∀ h : BHist, morseBoundaryDecodeBHist (morseBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def morseBoundaryFields : MorseBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MorseBoundaryUp.mk X G S F B H C P N => [X, G, S, F, B, H, C, P, N]

def morseBoundaryToEventFlow : MorseBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (morseBoundaryFields x).map morseBoundaryEncodeBHist

private def morseBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => morseBoundaryEventAt index rest

def morseBoundaryFromEventFlow (ef : EventFlow) : Option MorseBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MorseBoundaryUp.mk
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 0 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 1 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 2 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 3 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 4 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 5 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 6 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 7 ef))
      (morseBoundaryDecodeBHist (morseBoundaryEventAt 8 ef)))

private theorem MorseBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : MorseBoundaryUp) :
    morseBoundaryFromEventFlow (morseBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X G S F B H C P N =>
      change
        some
          (MorseBoundaryUp.mk
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist X))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist G))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist S))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist F))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist B))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist H))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist C))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist P))
            (morseBoundaryDecodeBHist (morseBoundaryEncodeBHist N))) =
          some (MorseBoundaryUp.mk X G S F B H C P N)
      rw [morseBoundary_decode_encode_bhist X, morseBoundary_decode_encode_bhist G,
        morseBoundary_decode_encode_bhist S, morseBoundary_decode_encode_bhist F,
        morseBoundary_decode_encode_bhist B, morseBoundary_decode_encode_bhist H,
        morseBoundary_decode_encode_bhist C, morseBoundary_decode_encode_bhist P,
        morseBoundary_decode_encode_bhist N]

private theorem MorseBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MorseBoundaryUp} :
    morseBoundaryToEventFlow x = morseBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      morseBoundaryFromEventFlow (morseBoundaryToEventFlow x) =
        morseBoundaryFromEventFlow (morseBoundaryToEventFlow y) :=
    congrArg morseBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MorseBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MorseBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance morseBoundaryBHistCarrier : BHistCarrier MorseBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := morseBoundaryToEventFlow
  fromEventFlow := morseBoundaryFromEventFlow

instance morseBoundaryChapterTasteGate : ChapterTasteGate MorseBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change morseBoundaryFromEventFlow (morseBoundaryToEventFlow x) = some x
    exact MorseBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MorseBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MorseBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, morseBoundaryDecodeBHist (morseBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MorseBoundaryUp) ∧
        Nonempty (ChapterTasteGate MorseBoundaryUp) ∧
          morseBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨morseBoundary_decode_encode_bhist, ⟨morseBoundaryBHistCarrier⟩,
      ⟨morseBoundaryChapterTasteGate⟩, rfl⟩

end BEDC.Derived.MorseBoundaryUp
