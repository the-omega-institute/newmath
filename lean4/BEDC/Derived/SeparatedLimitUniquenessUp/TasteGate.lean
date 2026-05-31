import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedLimitUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedLimitUniquenessUp : Type where
  | mk (L0 L1 Q M Z S H C P N : BHist) : SeparatedLimitUniquenessUp
  deriving DecidableEq

def separatedLimitUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedLimitUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedLimitUniquenessEncodeBHist h

def separatedLimitUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedLimitUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedLimitUniquenessDecodeBHist tail)

private theorem separatedLimitUniquenessDecode_encode_bhist :
    ∀ h : BHist,
      separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def separatedLimitUniquenessToEventFlow : SeparatedLimitUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedLimitUniquenessUp.mk L0 L1 Q M Z S H C P N =>
      [[BMark.b0],
        separatedLimitUniquenessEncodeBHist L0,
        [BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist L1,
        [BMark.b1, BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        separatedLimitUniquenessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        separatedLimitUniquenessEncodeBHist N]

private def separatedLimitUniquenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedLimitUniquenessEventAtDefault index rest

def separatedLimitUniquenessFromEventFlow (ef : EventFlow) :
    Option SeparatedLimitUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparatedLimitUniquenessUp.mk
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 1 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 3 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 5 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 7 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 9 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 11 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 13 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 15 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 17 ef))
      (separatedLimitUniquenessDecodeBHist (separatedLimitUniquenessEventAtDefault 19 ef)))

private theorem separatedLimitUniqueness_round_trip :
    ∀ x : SeparatedLimitUniquenessUp,
      separatedLimitUniquenessFromEventFlow (separatedLimitUniquenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L0 L1 Q M Z S H C P N =>
      change
        some
          (SeparatedLimitUniquenessUp.mk
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist L0))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist L1))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist Q))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist M))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist Z))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist S))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist H))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist C))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist P))
            (separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist N))) =
          some (SeparatedLimitUniquenessUp.mk L0 L1 Q M Z S H C P N)
      rw [separatedLimitUniquenessDecode_encode_bhist L0,
        separatedLimitUniquenessDecode_encode_bhist L1,
        separatedLimitUniquenessDecode_encode_bhist Q,
        separatedLimitUniquenessDecode_encode_bhist M,
        separatedLimitUniquenessDecode_encode_bhist Z,
        separatedLimitUniquenessDecode_encode_bhist S,
        separatedLimitUniquenessDecode_encode_bhist H,
        separatedLimitUniquenessDecode_encode_bhist C,
        separatedLimitUniquenessDecode_encode_bhist P,
        separatedLimitUniquenessDecode_encode_bhist N]

private theorem separatedLimitUniquenessToEventFlow_injective
    {x y : SeparatedLimitUniquenessUp} :
    separatedLimitUniquenessToEventFlow x =
      separatedLimitUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedLimitUniquenessFromEventFlow (separatedLimitUniquenessToEventFlow x) =
        separatedLimitUniquenessFromEventFlow (separatedLimitUniquenessToEventFlow y) :=
    congrArg separatedLimitUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (separatedLimitUniqueness_round_trip x).symm
      (Eq.trans hread (separatedLimitUniqueness_round_trip y)))

instance separatedLimitUniquenessBHistCarrier : BHistCarrier SeparatedLimitUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedLimitUniquenessToEventFlow
  fromEventFlow := separatedLimitUniquenessFromEventFlow

instance separatedLimitUniquenessChapterTasteGate :
    ChapterTasteGate SeparatedLimitUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedLimitUniquenessFromEventFlow (separatedLimitUniquenessToEventFlow x) =
        some x
    exact separatedLimitUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separatedLimitUniquenessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SeparatedLimitUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedLimitUniquenessChapterTasteGate

theorem SeparatedLimitUniquenessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SeparatedLimitUniquenessUp) ∧
      separatedLimitUniquenessEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ h : BHist,
          separatedLimitUniquenessDecodeBHist
              (separatedLimitUniquenessEncodeBHist h) =
            h) ∧
          (∀ x : SeparatedLimitUniquenessUp,
            separatedLimitUniquenessFromEventFlow (separatedLimitUniquenessToEventFlow x) =
              some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨separatedLimitUniquenessChapterTasteGate⟩, rfl,
      separatedLimitUniquenessDecode_encode_bhist,
      separatedLimitUniqueness_round_trip⟩

end BEDC.Derived.SeparatedLimitUniquenessUp
