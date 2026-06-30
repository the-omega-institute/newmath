import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactModulusSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactModulusSelectorUp : Type where
  | mk (K T F U D W R A H C P N : BHist) : CompactModulusSelectorUp
  deriving DecidableEq

def compactModulusSelectorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactModulusSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactModulusSelectorEncodeBHist h

def compactModulusSelectorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactModulusSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactModulusSelectorDecodeBHist tail)

private theorem compactModulusSelectorDecode_encode_bhist :
    forall h : BHist, compactModulusSelectorDecodeBHist
      (compactModulusSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactModulusSelectorToEventFlow : CompactModulusSelectorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactModulusSelectorUp.mk K T F U D W R A H C P N =>
      [[BMark.b0],
        compactModulusSelectorEncodeBHist K,
        [BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compactModulusSelectorEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusSelectorEncodeBHist N]

private def compactModulusSelectorEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactModulusSelectorEventAt index rest

def compactModulusSelectorFromEventFlow (ef : EventFlow) :
    Option CompactModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactModulusSelectorUp.mk
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 1 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 3 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 5 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 7 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 9 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 11 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 13 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 15 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 17 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 19 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 21 ef))
      (compactModulusSelectorDecodeBHist (compactModulusSelectorEventAt 23 ef)))

private theorem compactModulusSelector_round_trip :
    forall x : CompactModulusSelectorUp,
      compactModulusSelectorFromEventFlow
        (compactModulusSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K T F U D W R A H C P N =>
      change
        some
          (CompactModulusSelectorUp.mk
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist K))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist T))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist F))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist U))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist D))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist W))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist R))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist A))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist H))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist C))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist P))
            (compactModulusSelectorDecodeBHist (compactModulusSelectorEncodeBHist N))) =
          some (CompactModulusSelectorUp.mk K T F U D W R A H C P N)
      rw [compactModulusSelectorDecode_encode_bhist K,
        compactModulusSelectorDecode_encode_bhist T,
        compactModulusSelectorDecode_encode_bhist F,
        compactModulusSelectorDecode_encode_bhist U,
        compactModulusSelectorDecode_encode_bhist D,
        compactModulusSelectorDecode_encode_bhist W,
        compactModulusSelectorDecode_encode_bhist R,
        compactModulusSelectorDecode_encode_bhist A,
        compactModulusSelectorDecode_encode_bhist H,
        compactModulusSelectorDecode_encode_bhist C,
        compactModulusSelectorDecode_encode_bhist P,
        compactModulusSelectorDecode_encode_bhist N]

private theorem compactModulusSelectorToEventFlow_injective
    {x y : CompactModulusSelectorUp} :
    compactModulusSelectorToEventFlow x = compactModulusSelectorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactModulusSelectorFromEventFlow (compactModulusSelectorToEventFlow x) =
        compactModulusSelectorFromEventFlow (compactModulusSelectorToEventFlow y) :=
    congrArg compactModulusSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (compactModulusSelector_round_trip x).symm
      (Eq.trans hread (compactModulusSelector_round_trip y)))

instance compactModulusSelectorBHistCarrier : BHistCarrier CompactModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactModulusSelectorToEventFlow
  fromEventFlow := compactModulusSelectorFromEventFlow

instance compactModulusSelectorChapterTasteGate :
    ChapterTasteGate CompactModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactModulusSelectorFromEventFlow
      (compactModulusSelectorToEventFlow x) = some x
    exact compactModulusSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactModulusSelectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactModulusSelectorChapterTasteGate

theorem CompactModulusSelectorTasteGate_single_carrier_alignment :
    (forall h : BHist, compactModulusSelectorDecodeBHist
      (compactModulusSelectorEncodeBHist h) = h) ∧
      (forall x : CompactModulusSelectorUp,
        compactModulusSelectorFromEventFlow
          (compactModulusSelectorToEventFlow x) = some x) ∧
        (forall {x y : CompactModulusSelectorUp},
          compactModulusSelectorToEventFlow x = compactModulusSelectorToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactModulusSelectorDecode_encode_bhist,
      compactModulusSelector_round_trip,
      fun {x y} heq => compactModulusSelectorToEventFlow_injective heq⟩

end BEDC.Derived.CompactModulusSelectorUp
