import BEDC.Derived.ConstructiveHeineBorelIntervalUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveHeineBorelIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def constructiveHeineBorelIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveHeineBorelIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveHeineBorelIntervalEncodeBHist h

def constructiveHeineBorelIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveHeineBorelIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveHeineBorelIntervalDecodeBHist tail)

private theorem ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveHeineBorelIntervalDecodeBHist
          (constructiveHeineBorelIntervalEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveHeineBorelIntervalFields :
    ConstructiveHeineBorelIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveHeineBorelIntervalUp.mk I D R S E M U H C P N =>
      [I, D, R, S, E, M, U, H, C, P, N]

def constructiveHeineBorelIntervalToEventFlow :
    ConstructiveHeineBorelIntervalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (constructiveHeineBorelIntervalFields x).map
    constructiveHeineBorelIntervalEncodeBHist

private def constructiveHeineBorelIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveHeineBorelIntervalEventAtDefault index rest

def constructiveHeineBorelIntervalFromEventFlow
    (eventFlow : EventFlow) : Option ConstructiveHeineBorelIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveHeineBorelIntervalUp.mk
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 0 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 1 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 2 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 3 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 4 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 5 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 6 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 7 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 8 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 9 eventFlow))
      (constructiveHeineBorelIntervalDecodeBHist
        (constructiveHeineBorelIntervalEventAtDefault 10 eventFlow)))

instance constructiveHeineBorelIntervalBHistCarrier :
    BHistCarrier ConstructiveHeineBorelIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveHeineBorelIntervalToEventFlow
  fromEventFlow := constructiveHeineBorelIntervalFromEventFlow

private theorem ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveHeineBorelIntervalUp,
      constructiveHeineBorelIntervalFromEventFlow
          (constructiveHeineBorelIntervalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I D R S E M U H C P N =>
      change
        some
            (ConstructiveHeineBorelIntervalUp.mk
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist I))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist D))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist R))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist S))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist E))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist M))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist U))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist H))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist C))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist P))
              (constructiveHeineBorelIntervalDecodeBHist
                (constructiveHeineBorelIntervalEncodeBHist N))) =
          some (ConstructiveHeineBorelIntervalUp.mk I D R S E M U H C P N)
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode I]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode D]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode R]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode S]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode E]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode M]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode U]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode H]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode C]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode P]
      rw [ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode N]

private theorem ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveHeineBorelIntervalUp} :
    constructiveHeineBorelIntervalToEventFlow x =
        constructiveHeineBorelIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveHeineBorelIntervalFromEventFlow
          (constructiveHeineBorelIntervalToEventFlow x) =
        constructiveHeineBorelIntervalFromEventFlow
          (constructiveHeineBorelIntervalToEventFlow y) :=
    congrArg constructiveHeineBorelIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_round_trip y)))

def constructiveHeineBorelIntervalChapterTasteGate :
    ChapterTasteGate ConstructiveHeineBorelIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveHeineBorelIntervalFromEventFlow
          (constructiveHeineBorelIntervalToEventFlow x) =
        some x
    exact ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance constructiveHeineBorelIntervalChapterTasteGateInstance :
    ChapterTasteGate ConstructiveHeineBorelIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveHeineBorelIntervalChapterTasteGate

theorem ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      constructiveHeineBorelIntervalDecodeBHist
          (constructiveHeineBorelIntervalEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier ConstructiveHeineBorelIntervalUp) ∧
        Nonempty (ChapterTasteGate ConstructiveHeineBorelIntervalUp) ∧
          constructiveHeineBorelIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveHeineBorelIntervalTasteGate_single_carrier_alignment_decode,
      ⟨constructiveHeineBorelIntervalBHistCarrier⟩,
      ⟨constructiveHeineBorelIntervalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ConstructiveHeineBorelIntervalUp
