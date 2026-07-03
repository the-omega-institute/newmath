import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WhiteheadProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WhiteheadProductUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (sourceLeft sourceRight mapLeft mapRight boundary commutator bracket transport replay
        provenance name : BHist) →
        WhiteheadProductUp
  deriving DecidableEq

def whiteheadProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: whiteheadProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: whiteheadProductEncodeBHist h

def whiteheadProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (whiteheadProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (whiteheadProductDecodeBHist tail)

private theorem WhiteheadProductTasteGate_single_carrier_alignment_decode_encode
    (h : BHist) :
    whiteheadProductDecodeBHist (whiteheadProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def whiteheadProductFields : WhiteheadProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WhiteheadProductUp.mk sourceLeft sourceRight mapLeft mapRight boundary commutator bracket
      transport replay provenance name =>
      [sourceLeft, sourceRight, mapLeft, mapRight, boundary, commutator, bracket, transport,
        replay, provenance, name]

def whiteheadProductToEventFlow : WhiteheadProductUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (whiteheadProductFields x).map whiteheadProductEncodeBHist

private def whiteheadProductRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => whiteheadProductRawAt index rest

def whiteheadProductFromEventFlow (flow : EventFlow) : Option WhiteheadProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WhiteheadProductUp.mk
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 0 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 1 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 2 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 3 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 4 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 5 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 6 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 7 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 8 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 9 flow))
      (whiteheadProductDecodeBHist (whiteheadProductRawAt 10 flow)))

private theorem WhiteheadProductTasteGate_single_carrier_alignment_round_trip
    (x : WhiteheadProductUp) :
    whiteheadProductFromEventFlow (whiteheadProductToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk sourceLeft sourceRight mapLeft mapRight boundary commutator bracket transport replay
      provenance name =>
      change
        some
            (WhiteheadProductUp.mk
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist sourceLeft))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist sourceRight))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist mapLeft))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist mapRight))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist boundary))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist commutator))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist bracket))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist transport))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist replay))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist provenance))
              (whiteheadProductDecodeBHist (whiteheadProductEncodeBHist name))) =
          some
            (WhiteheadProductUp.mk sourceLeft sourceRight mapLeft mapRight boundary commutator
              bracket transport replay provenance name)
      rw [WhiteheadProductTasteGate_single_carrier_alignment_decode_encode sourceLeft,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode sourceRight,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode mapLeft,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode mapRight,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode boundary,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode commutator,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode bracket,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode transport,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode replay,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode provenance,
        WhiteheadProductTasteGate_single_carrier_alignment_decode_encode name]

private theorem WhiteheadProductTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WhiteheadProductUp} :
    whiteheadProductToEventFlow x = whiteheadProductToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      whiteheadProductFromEventFlow (whiteheadProductToEventFlow x) =
        whiteheadProductFromEventFlow (whiteheadProductToEventFlow y) :=
    congrArg whiteheadProductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WhiteheadProductTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WhiteheadProductTasteGate_single_carrier_alignment_round_trip y)))

instance whiteheadProductBHistCarrier : BHistCarrier WhiteheadProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := whiteheadProductToEventFlow
  fromEventFlow := whiteheadProductFromEventFlow

instance whiteheadProductChapterTasteGate : ChapterTasteGate WhiteheadProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change whiteheadProductFromEventFlow (whiteheadProductToEventFlow x) = some x
    exact WhiteheadProductTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WhiteheadProductTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem WhiteheadProductTasteGate_single_carrier_alignment :
    (∀ h : BHist, whiteheadProductDecodeBHist (whiteheadProductEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier WhiteheadProductUp) ∧
        Nonempty (ChapterTasteGate WhiteheadProductUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact WhiteheadProductTasteGate_single_carrier_alignment_decode_encode h
  · constructor
    · exact ⟨whiteheadProductBHistCarrier⟩
    · exact ⟨whiteheadProductChapterTasteGate⟩

end BEDC.Derived.WhiteheadProductUp
