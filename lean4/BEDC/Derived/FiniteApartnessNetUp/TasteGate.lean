import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteApartnessNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteApartnessNetUp : Type where
  | mk (C D A V H K P N : BHist) : FiniteApartnessNetUp
  deriving DecidableEq

def finiteApartnessNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteApartnessNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteApartnessNetEncodeBHist h

def finiteApartnessNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteApartnessNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteApartnessNetDecodeBHist tail)

private theorem finiteApartnessNetDecode_encode_bhist :
    ∀ h : BHist, finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteApartnessNetToEventFlow : FiniteApartnessNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteApartnessNetUp.mk C D A V H K P N =>
      [finiteApartnessNetEncodeBHist C,
        finiteApartnessNetEncodeBHist D,
        finiteApartnessNetEncodeBHist A,
        finiteApartnessNetEncodeBHist V,
        finiteApartnessNetEncodeBHist H,
        finiteApartnessNetEncodeBHist K,
        finiteApartnessNetEncodeBHist P,
        finiteApartnessNetEncodeBHist N]

def finiteApartnessNetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteApartnessNetEventAtDefault index rest

def finiteApartnessNetFromEventFlow (ef : EventFlow) : Option FiniteApartnessNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteApartnessNetUp.mk
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 0 ef))
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 1 ef))
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 2 ef))
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 3 ef))
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 4 ef))
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 5 ef))
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 6 ef))
      (finiteApartnessNetDecodeBHist (finiteApartnessNetEventAtDefault 7 ef)))

private theorem finiteApartnessNet_round_trip :
    ∀ x : FiniteApartnessNetUp,
      finiteApartnessNetFromEventFlow (finiteApartnessNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk C D A V H K P N =>
      change
        some
          (FiniteApartnessNetUp.mk
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist C))
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist D))
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist A))
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist V))
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist H))
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist K))
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist P))
            (finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist N))) =
          some (FiniteApartnessNetUp.mk C D A V H K P N)
      rw [finiteApartnessNetDecode_encode_bhist C,
        finiteApartnessNetDecode_encode_bhist D,
        finiteApartnessNetDecode_encode_bhist A,
        finiteApartnessNetDecode_encode_bhist V,
        finiteApartnessNetDecode_encode_bhist H,
        finiteApartnessNetDecode_encode_bhist K,
        finiteApartnessNetDecode_encode_bhist P,
        finiteApartnessNetDecode_encode_bhist N]

private theorem finiteApartnessNetToEventFlow_injective {x y : FiniteApartnessNetUp} :
    finiteApartnessNetToEventFlow x = finiteApartnessNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteApartnessNetFromEventFlow (finiteApartnessNetToEventFlow x) =
        finiteApartnessNetFromEventFlow (finiteApartnessNetToEventFlow y) :=
    congrArg finiteApartnessNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteApartnessNet_round_trip x).symm
      (Eq.trans hread (finiteApartnessNet_round_trip y)))

instance finiteApartnessNetBHistCarrier :
    BHistCarrier FiniteApartnessNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteApartnessNetToEventFlow
  fromEventFlow := finiteApartnessNetFromEventFlow

instance finiteApartnessNetChapterTasteGate :
    ChapterTasteGate FiniteApartnessNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteApartnessNetFromEventFlow (finiteApartnessNetToEventFlow x) = some x
    exact finiteApartnessNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteApartnessNetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteApartnessNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteApartnessNetChapterTasteGate

theorem FiniteApartnessNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteApartnessNetDecodeBHist (finiteApartnessNetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteApartnessNetUp) ∧
        Nonempty (ChapterTasteGate FiniteApartnessNetUp) ∧
          finiteApartnessNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨finiteApartnessNetDecode_encode_bhist,
      Nonempty.intro finiteApartnessNetBHistCarrier,
      Nonempty.intro finiteApartnessNetChapterTasteGate,
      rfl⟩

end BEDC.Derived.FiniteApartnessNetUp
