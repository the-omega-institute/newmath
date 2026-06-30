import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KirchhoffMatrixTreeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KirchhoffMatrixTreeUp : Type where
  | mk (G E L M D S T H C P N : BHist) : KirchhoffMatrixTreeUp
  deriving DecidableEq

def kirchhoffMatrixTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kirchhoffMatrixTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kirchhoffMatrixTreeEncodeBHist h

def kirchhoffMatrixTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kirchhoffMatrixTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kirchhoffMatrixTreeDecodeBHist tail)

private theorem kirchhoffMatrixTree_decode_encode_bhist :
    ∀ h : BHist, kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kirchhoffMatrixTreeToEventFlow : KirchhoffMatrixTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KirchhoffMatrixTreeUp.mk G E L M D S T H C P N =>
      [kirchhoffMatrixTreeEncodeBHist G,
        kirchhoffMatrixTreeEncodeBHist E,
        kirchhoffMatrixTreeEncodeBHist L,
        kirchhoffMatrixTreeEncodeBHist M,
        kirchhoffMatrixTreeEncodeBHist D,
        kirchhoffMatrixTreeEncodeBHist S,
        kirchhoffMatrixTreeEncodeBHist T,
        kirchhoffMatrixTreeEncodeBHist H,
        kirchhoffMatrixTreeEncodeBHist C,
        kirchhoffMatrixTreeEncodeBHist P,
        kirchhoffMatrixTreeEncodeBHist N]

private def kirchhoffMatrixTreeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kirchhoffMatrixTreeEventAtDefault index rest

def kirchhoffMatrixTreeFromEventFlow (ef : EventFlow) :
    Option KirchhoffMatrixTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KirchhoffMatrixTreeUp.mk
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 0 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 1 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 2 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 3 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 4 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 5 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 6 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 7 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 8 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 9 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAtDefault 10 ef)))

private theorem kirchhoffMatrixTree_round_trip :
    ∀ x : KirchhoffMatrixTreeUp,
      kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G E L M D S T H C P N =>
      change
        some
          (KirchhoffMatrixTreeUp.mk
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist G))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist E))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist L))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist M))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist D))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist S))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist T))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist H))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist C))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist P))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist N))) =
          some (KirchhoffMatrixTreeUp.mk G E L M D S T H C P N)
      rw [kirchhoffMatrixTree_decode_encode_bhist G,
        kirchhoffMatrixTree_decode_encode_bhist E,
        kirchhoffMatrixTree_decode_encode_bhist L,
        kirchhoffMatrixTree_decode_encode_bhist M,
        kirchhoffMatrixTree_decode_encode_bhist D,
        kirchhoffMatrixTree_decode_encode_bhist S,
        kirchhoffMatrixTree_decode_encode_bhist T,
        kirchhoffMatrixTree_decode_encode_bhist H,
        kirchhoffMatrixTree_decode_encode_bhist C,
        kirchhoffMatrixTree_decode_encode_bhist P,
        kirchhoffMatrixTree_decode_encode_bhist N]

private theorem kirchhoffMatrixTreeToEventFlow_injective
    {x y : KirchhoffMatrixTreeUp} :
    kirchhoffMatrixTreeToEventFlow x = kirchhoffMatrixTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow x) =
        kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow y) :=
    congrArg kirchhoffMatrixTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kirchhoffMatrixTree_round_trip x).symm
      (Eq.trans hread (kirchhoffMatrixTree_round_trip y)))

instance kirchhoffMatrixTreeBHistCarrier : BHistCarrier KirchhoffMatrixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kirchhoffMatrixTreeToEventFlow
  fromEventFlow := kirchhoffMatrixTreeFromEventFlow

instance kirchhoffMatrixTreeChapterTasteGate : ChapterTasteGate KirchhoffMatrixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow x) = some x
    exact kirchhoffMatrixTree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kirchhoffMatrixTreeToEventFlow_injective heq)

theorem KirchhoffMatrixTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist, kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KirchhoffMatrixTreeUp) ∧
        Nonempty (ChapterTasteGate KirchhoffMatrixTreeUp) ∧
          kirchhoffMatrixTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kirchhoffMatrixTree_decode_encode_bhist
  · constructor
    · exact Nonempty.intro kirchhoffMatrixTreeBHistCarrier
    · constructor
      · exact Nonempty.intro kirchhoffMatrixTreeChapterTasteGate
      · rfl

end BEDC.Derived.KirchhoffMatrixTreeUp.TasteGate
