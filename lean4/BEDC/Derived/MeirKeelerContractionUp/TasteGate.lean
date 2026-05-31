import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeirKeelerContractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeirKeelerContractionUp : Type where
  | mk (X d T E I L H C P N : BHist) : MeirKeelerContractionUp
  deriving DecidableEq

def meirKeelerContractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: meirKeelerContractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: meirKeelerContractionEncodeBHist h

def meirKeelerContractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (meirKeelerContractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (meirKeelerContractionDecodeBHist tail)

private theorem meirKeelerContraction_decode_encode_bhist :
    ∀ h : BHist,
      meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def meirKeelerContractionFields : MeirKeelerContractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MeirKeelerContractionUp.mk X d T E I L H C P N => [X, d, T, E, I, L, H, C, P, N]

def meirKeelerContractionToEventFlow : MeirKeelerContractionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (meirKeelerContractionFields x).map meirKeelerContractionEncodeBHist

private def meirKeelerContractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => meirKeelerContractionEventAtDefault index rest

def meirKeelerContractionFromEventFlow (ef : EventFlow) : Option MeirKeelerContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MeirKeelerContractionUp.mk
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 0 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 1 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 2 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 3 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 4 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 5 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 6 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 7 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 8 ef))
      (meirKeelerContractionDecodeBHist (meirKeelerContractionEventAtDefault 9 ef)))

private theorem meirKeelerContraction_round_trip :
    ∀ x : MeirKeelerContractionUp,
      meirKeelerContractionFromEventFlow
        (meirKeelerContractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d T E I L H C P N =>
      change
        some
          (MeirKeelerContractionUp.mk
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist X))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist d))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist T))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist E))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist I))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist L))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist H))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist C))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist P))
            (meirKeelerContractionDecodeBHist (meirKeelerContractionEncodeBHist N))) =
          some (MeirKeelerContractionUp.mk X d T E I L H C P N)
      rw [meirKeelerContraction_decode_encode_bhist X,
        meirKeelerContraction_decode_encode_bhist d,
        meirKeelerContraction_decode_encode_bhist T,
        meirKeelerContraction_decode_encode_bhist E,
        meirKeelerContraction_decode_encode_bhist I,
        meirKeelerContraction_decode_encode_bhist L,
        meirKeelerContraction_decode_encode_bhist H,
        meirKeelerContraction_decode_encode_bhist C,
        meirKeelerContraction_decode_encode_bhist P,
        meirKeelerContraction_decode_encode_bhist N]

private theorem meirKeelerContractionToEventFlow_injective
    {x y : MeirKeelerContractionUp} :
    meirKeelerContractionToEventFlow x = meirKeelerContractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      meirKeelerContractionFromEventFlow (meirKeelerContractionToEventFlow x) =
        meirKeelerContractionFromEventFlow (meirKeelerContractionToEventFlow y) :=
    congrArg meirKeelerContractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (meirKeelerContraction_round_trip x).symm
      (Eq.trans hread (meirKeelerContraction_round_trip y)))

instance meirKeelerContractionBHistCarrier : BHistCarrier MeirKeelerContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := meirKeelerContractionToEventFlow
  fromEventFlow := meirKeelerContractionFromEventFlow

instance meirKeelerContractionChapterTasteGate : ChapterTasteGate MeirKeelerContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change meirKeelerContractionFromEventFlow (meirKeelerContractionToEventFlow x) = some x
    exact meirKeelerContraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (meirKeelerContractionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MeirKeelerContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  meirKeelerContractionChapterTasteGate

theorem MeirKeelerContractionTasteGate_single_carrier_alignment :
    (∀ x : MeirKeelerContractionUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (∀ x y : MeirKeelerContractionUp,
        x ≠ y → BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro x
    change meirKeelerContractionFromEventFlow (meirKeelerContractionToEventFlow x) = some x
    exact meirKeelerContraction_round_trip x
  · intro x y hxy heq
    change meirKeelerContractionToEventFlow x = meirKeelerContractionToEventFlow y at heq
    exact hxy (meirKeelerContractionToEventFlow_injective heq)

end BEDC.Derived.MeirKeelerContractionUp
