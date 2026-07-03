import BEDC.Derived.RealCauchyModulusSelectorUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyModulusSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realCauchyModulusSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyModulusSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyModulusSelectorEncodeBHist h

def realCauchyModulusSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyModulusSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyModulusSelectorDecodeBHist tail)

private theorem RealCauchyModulusSelectorTasteGate_decode_encode :
    ∀ h : BHist,
      realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyModulusSelectorToEventFlow : RealCauchyModulusSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyModulusSelectorUp.mk M S D Q E R H P N =>
      [realCauchyModulusSelectorEncodeBHist M,
        realCauchyModulusSelectorEncodeBHist S,
        realCauchyModulusSelectorEncodeBHist D,
        realCauchyModulusSelectorEncodeBHist Q,
        realCauchyModulusSelectorEncodeBHist E,
        realCauchyModulusSelectorEncodeBHist R,
        realCauchyModulusSelectorEncodeBHist H,
        realCauchyModulusSelectorEncodeBHist P,
        realCauchyModulusSelectorEncodeBHist N]

private def realCauchyModulusSelectorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyModulusSelectorEventAt index rest

def realCauchyModulusSelectorFromEventFlow
    (ef : EventFlow) : Option RealCauchyModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCauchyModulusSelectorUp.mk
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 0 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 1 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 2 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 3 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 4 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 5 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 6 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 7 ef))
      (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEventAt 8 ef)))

private theorem RealCauchyModulusSelectorTasteGate_round_trip :
    ∀ x : RealCauchyModulusSelectorUp,
      realCauchyModulusSelectorFromEventFlow
          (realCauchyModulusSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D Q E R H P N =>
      change
        some
          (RealCauchyModulusSelectorUp.mk
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist M))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist S))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist D))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist Q))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist E))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist R))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist H))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist P))
            (realCauchyModulusSelectorDecodeBHist (realCauchyModulusSelectorEncodeBHist N))) =
          some (RealCauchyModulusSelectorUp.mk M S D Q E R H P N)
      rw [RealCauchyModulusSelectorTasteGate_decode_encode M,
        RealCauchyModulusSelectorTasteGate_decode_encode S,
        RealCauchyModulusSelectorTasteGate_decode_encode D,
        RealCauchyModulusSelectorTasteGate_decode_encode Q,
        RealCauchyModulusSelectorTasteGate_decode_encode E,
        RealCauchyModulusSelectorTasteGate_decode_encode R,
        RealCauchyModulusSelectorTasteGate_decode_encode H,
        RealCauchyModulusSelectorTasteGate_decode_encode P,
        RealCauchyModulusSelectorTasteGate_decode_encode N]

private theorem RealCauchyModulusSelectorTasteGate_toEventFlow_injective
    {x y : RealCauchyModulusSelectorUp} :
    realCauchyModulusSelectorToEventFlow x = realCauchyModulusSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyModulusSelectorFromEventFlow (realCauchyModulusSelectorToEventFlow x) =
        realCauchyModulusSelectorFromEventFlow (realCauchyModulusSelectorToEventFlow y) :=
    congrArg realCauchyModulusSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealCauchyModulusSelectorTasteGate_round_trip x).symm
      (Eq.trans hread (RealCauchyModulusSelectorTasteGate_round_trip y)))

instance realCauchyModulusSelectorBHistCarrier :
    BHistCarrier RealCauchyModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyModulusSelectorToEventFlow
  fromEventFlow := realCauchyModulusSelectorFromEventFlow

instance realCauchyModulusSelectorChapterTasteGate :
    ChapterTasteGate RealCauchyModulusSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCauchyModulusSelectorFromEventFlow (realCauchyModulusSelectorToEventFlow x) =
        some x
    exact RealCauchyModulusSelectorTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealCauchyModulusSelectorTasteGate_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCauchyModulusSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyModulusSelectorChapterTasteGate

theorem RealCauchyModulusSelectorTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RealCauchyModulusSelectorUp) ∧
      Nonempty (ChapterTasteGate RealCauchyModulusSelectorUp) ∧
        (∀ h : BHist,
          realCauchyModulusSelectorDecodeBHist
              (realCauchyModulusSelectorEncodeBHist h) =
            h) ∧
          (∀ x : RealCauchyModulusSelectorUp,
            realCauchyModulusSelectorFromEventFlow
                (realCauchyModulusSelectorToEventFlow x) =
              some x) ∧
            realCauchyModulusSelectorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨realCauchyModulusSelectorBHistCarrier⟩,
      ⟨realCauchyModulusSelectorChapterTasteGate⟩,
      RealCauchyModulusSelectorTasteGate_decode_encode,
      RealCauchyModulusSelectorTasteGate_round_trip,
      rfl⟩

end BEDC.Derived.RealCauchyModulusSelectorUp
