import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuasiPolishSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuasiPolishSpaceUp : Type where
  | mk (T B S L P W H C G N : BHist) : QuasiPolishSpaceUp
  deriving DecidableEq

def quasiPolishSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quasiPolishSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quasiPolishSpaceEncodeBHist h

def quasiPolishSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quasiPolishSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quasiPolishSpaceDecodeBHist tail)

private theorem quasiPolishSpaceDecodeEncode :
    forall h : BHist,
      quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quasiPolishSpaceFields : QuasiPolishSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuasiPolishSpaceUp.mk T B S L P W H C G N => [T, B, S, L, P, W, H, C, G, N]

def quasiPolishSpaceToEventFlow : QuasiPolishSpaceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (quasiPolishSpaceFields x).map quasiPolishSpaceEncodeBHist

private def quasiPolishSpaceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => quasiPolishSpaceEventAtDefault index rest

def quasiPolishSpaceFromEventFlow (ef : EventFlow) : Option QuasiPolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (QuasiPolishSpaceUp.mk
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 0 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 1 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 2 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 3 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 4 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 5 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 6 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 7 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 8 ef))
      (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEventAtDefault 9 ef)))

private theorem quasiPolishSpaceRoundTrip :
    forall x : QuasiPolishSpaceUp,
      quasiPolishSpaceFromEventFlow (quasiPolishSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B S L P W H C G N =>
      change
        some
          (QuasiPolishSpaceUp.mk
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist T))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist B))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist S))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist L))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist P))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist W))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist H))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist C))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist G))
            (quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist N))) =
          some (QuasiPolishSpaceUp.mk T B S L P W H C G N)
      rw [quasiPolishSpaceDecodeEncode T, quasiPolishSpaceDecodeEncode B,
        quasiPolishSpaceDecodeEncode S, quasiPolishSpaceDecodeEncode L,
        quasiPolishSpaceDecodeEncode P, quasiPolishSpaceDecodeEncode W,
        quasiPolishSpaceDecodeEncode H, quasiPolishSpaceDecodeEncode C,
        quasiPolishSpaceDecodeEncode G, quasiPolishSpaceDecodeEncode N]

private theorem quasiPolishSpaceToEventFlow_injective
    {x y : QuasiPolishSpaceUp} :
    quasiPolishSpaceToEventFlow x = quasiPolishSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quasiPolishSpaceFromEventFlow (quasiPolishSpaceToEventFlow x) =
        quasiPolishSpaceFromEventFlow (quasiPolishSpaceToEventFlow y) :=
    congrArg quasiPolishSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (quasiPolishSpaceRoundTrip x).symm
      (Eq.trans hread (quasiPolishSpaceRoundTrip y)))

instance quasiPolishSpaceBHistCarrier : BHistCarrier QuasiPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quasiPolishSpaceToEventFlow
  fromEventFlow := quasiPolishSpaceFromEventFlow

instance quasiPolishSpaceChapterTasteGate : ChapterTasteGate QuasiPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quasiPolishSpaceFromEventFlow (quasiPolishSpaceToEventFlow x) = some x
    exact quasiPolishSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (quasiPolishSpaceToEventFlow_injective heq)

theorem QuasiPolishSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, quasiPolishSpaceDecodeBHist (quasiPolishSpaceEncodeBHist h) = h) ∧
      (forall x : QuasiPolishSpaceUp,
        quasiPolishSpaceFromEventFlow (quasiPolishSpaceToEventFlow x) = some x) ∧
        (forall x y : QuasiPolishSpaceUp,
          quasiPolishSpaceToEventFlow x = quasiPolishSpaceToEventFlow y -> x = y) ∧
          quasiPolishSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨quasiPolishSpaceDecodeEncode,
      quasiPolishSpaceRoundTrip,
      (fun _x _y heq => quasiPolishSpaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.QuasiPolishSpaceUp.TasteGate
