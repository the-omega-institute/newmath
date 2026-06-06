import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyAlgebraCoherenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyAlgebraCoherenceUp : Type where
  | mk (L R W D A M S T C P N : BHist) : RegularCauchyAlgebraCoherenceUp
  deriving DecidableEq

def regularCauchyAlgebraCoherenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyAlgebraCoherenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyAlgebraCoherenceEncodeBHist h

def regularCauchyAlgebraCoherenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyAlgebraCoherenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyAlgebraCoherenceDecodeBHist tail)

private theorem regularCauchyAlgebraCoherence_decode_encode :
    ∀ h : BHist,
      regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyAlgebraCoherenceFields :
    RegularCauchyAlgebraCoherenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyAlgebraCoherenceUp.mk L R W D A M S T C P N =>
      [L, R, W, D, A, M, S, T, C, P, N]

def regularCauchyAlgebraCoherenceToEventFlow :
    RegularCauchyAlgebraCoherenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyAlgebraCoherenceFields x).map
      regularCauchyAlgebraCoherenceEncodeBHist

private def regularCauchyAlgebraCoherenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyAlgebraCoherenceEventAtDefault index rest

def regularCauchyAlgebraCoherenceFromEventFlow
    (ef : EventFlow) : Option RegularCauchyAlgebraCoherenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyAlgebraCoherenceUp.mk
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 0 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 1 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 2 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 3 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 4 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 5 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 6 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 7 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 8 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 9 ef))
      (regularCauchyAlgebraCoherenceDecodeBHist
        (regularCauchyAlgebraCoherenceEventAtDefault 10 ef)))

private theorem regularCauchyAlgebraCoherence_round_trip :
    ∀ x : RegularCauchyAlgebraCoherenceUp,
      regularCauchyAlgebraCoherenceFromEventFlow
        (regularCauchyAlgebraCoherenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R W D A M S T C P N =>
      change
        some
          (RegularCauchyAlgebraCoherenceUp.mk
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist L))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist R))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist W))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist D))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist A))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist M))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist S))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist T))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist C))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist P))
            (regularCauchyAlgebraCoherenceDecodeBHist
              (regularCauchyAlgebraCoherenceEncodeBHist N))) =
          some (RegularCauchyAlgebraCoherenceUp.mk L R W D A M S T C P N)
      rw [regularCauchyAlgebraCoherence_decode_encode L,
        regularCauchyAlgebraCoherence_decode_encode R,
        regularCauchyAlgebraCoherence_decode_encode W,
        regularCauchyAlgebraCoherence_decode_encode D,
        regularCauchyAlgebraCoherence_decode_encode A,
        regularCauchyAlgebraCoherence_decode_encode M,
        regularCauchyAlgebraCoherence_decode_encode S,
        regularCauchyAlgebraCoherence_decode_encode T,
        regularCauchyAlgebraCoherence_decode_encode C,
        regularCauchyAlgebraCoherence_decode_encode P,
        regularCauchyAlgebraCoherence_decode_encode N]

private theorem regularCauchyAlgebraCoherenceToEventFlow_injective
    {x y : RegularCauchyAlgebraCoherenceUp} :
    regularCauchyAlgebraCoherenceToEventFlow x =
      regularCauchyAlgebraCoherenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyAlgebraCoherenceFromEventFlow
          (regularCauchyAlgebraCoherenceToEventFlow x) =
        regularCauchyAlgebraCoherenceFromEventFlow
          (regularCauchyAlgebraCoherenceToEventFlow y) :=
    congrArg regularCauchyAlgebraCoherenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (regularCauchyAlgebraCoherence_round_trip x).symm
      (Eq.trans hread (regularCauchyAlgebraCoherence_round_trip y)))

instance regularCauchyAlgebraCoherenceBHistCarrier :
    BHistCarrier RegularCauchyAlgebraCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyAlgebraCoherenceToEventFlow
  fromEventFlow := regularCauchyAlgebraCoherenceFromEventFlow

instance regularCauchyAlgebraCoherenceChapterTasteGate :
    ChapterTasteGate RegularCauchyAlgebraCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyAlgebraCoherenceFromEventFlow
        (regularCauchyAlgebraCoherenceToEventFlow x) = some x
    exact regularCauchyAlgebraCoherence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyAlgebraCoherenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyAlgebraCoherenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyAlgebraCoherenceChapterTasteGate

theorem RegularCauchyAlgebraCoherenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyAlgebraCoherenceDecodeBHist
          (regularCauchyAlgebraCoherenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyAlgebraCoherenceUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyAlgebraCoherenceUp) ∧
      regularCauchyAlgebraCoherenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyAlgebraCoherence_decode_encode,
      ⟨regularCauchyAlgebraCoherenceBHistCarrier⟩,
      ⟨regularCauchyAlgebraCoherenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyAlgebraCoherenceUp
