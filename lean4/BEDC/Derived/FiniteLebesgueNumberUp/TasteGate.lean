import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteLebesgueNumberUp : Type where
  | mk (D M R S G E K H C P N : BHist) : FiniteLebesgueNumberUp

def finiteLebesgueNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteLebesgueNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteLebesgueNumberEncodeBHist h

def finiteLebesgueNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteLebesgueNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteLebesgueNumberDecodeBHist tail)

private theorem FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteLebesgueNumberFields : FiniteLebesgueNumberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteLebesgueNumberUp.mk D M R S G E K H C P N => [D, M, R, S, G, E, K, H, C, P, N]

def finiteLebesgueNumberToEventFlow : FiniteLebesgueNumberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteLebesgueNumberFields x).map finiteLebesgueNumberEncodeBHist

private def finiteLebesgueNumberEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteLebesgueNumberEventAtDefault index rest

def finiteLebesgueNumberFromEventFlow :
    EventFlow → Option FiniteLebesgueNumberUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (FiniteLebesgueNumberUp.mk
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 0 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 1 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 2 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 3 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 4 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 5 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 6 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 7 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 8 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 9 ef))
          (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEventAtDefault 10 ef)))

private theorem FiniteLebesgueNumberTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteLebesgueNumberUp,
      finiteLebesgueNumberFromEventFlow (finiteLebesgueNumberToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M R S G E K H C P N =>
      change
        some
          (FiniteLebesgueNumberUp.mk
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist D))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist M))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist R))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist S))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist G))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist E))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist K))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist H))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist C))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist P))
            (finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist N))) =
          some (FiniteLebesgueNumberUp.mk D M R S G E K H C P N)
      rw [FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode D,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode M,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode R,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode S,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode G,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode E,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode K,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode H,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode C,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode P,
        FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode N]

private theorem FiniteLebesgueNumberTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteLebesgueNumberUp} :
    finiteLebesgueNumberToEventFlow x = finiteLebesgueNumberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteLebesgueNumberFromEventFlow (finiteLebesgueNumberToEventFlow x) =
        finiteLebesgueNumberFromEventFlow (finiteLebesgueNumberToEventFlow y) :=
    congrArg finiteLebesgueNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteLebesgueNumberTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteLebesgueNumberTasteGate_single_carrier_alignment_round_trip y)))

instance finiteLebesgueNumberBHistCarrier :
    BHistCarrier FiniteLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteLebesgueNumberToEventFlow
  fromEventFlow := finiteLebesgueNumberFromEventFlow

instance finiteLebesgueNumberChapterTasteGate :
    ChapterTasteGate FiniteLebesgueNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteLebesgueNumberFromEventFlow (finiteLebesgueNumberToEventFlow x) = some x
    exact FiniteLebesgueNumberTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteLebesgueNumberTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteLebesgueNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteLebesgueNumberChapterTasteGate

theorem FiniteLebesgueNumberTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteLebesgueNumberDecodeBHist (finiteLebesgueNumberEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteLebesgueNumberUp) ∧
        Nonempty (ChapterTasteGate FiniteLebesgueNumberUp) ∧
          finiteLebesgueNumberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨FiniteLebesgueNumberTasteGate_single_carrier_alignment_decode,
      ⟨finiteLebesgueNumberBHistCarrier⟩,
      ⟨finiteLebesgueNumberChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteLebesgueNumberUp
