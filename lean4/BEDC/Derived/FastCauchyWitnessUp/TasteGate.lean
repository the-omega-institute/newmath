import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchyWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchyWitnessUp : Type where
  | mk (S W D R M E H C P N : BHist) : FastCauchyWitnessUp
  deriving DecidableEq

def fastCauchyWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchyWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchyWitnessEncodeBHist h

def fastCauchyWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchyWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchyWitnessDecodeBHist tail)

private theorem FastCauchyWitnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastCauchyWitnessFields : FastCauchyWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastCauchyWitnessUp.mk S W D R M E H C P N => [S, W, D, R, M, E, H, C, P, N]

def fastCauchyWitnessToEventFlow : FastCauchyWitnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fastCauchyWitnessFields x).map fastCauchyWitnessEncodeBHist

private def fastCauchyWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fastCauchyWitnessEventAtDefault index rest

def fastCauchyWitnessFromEventFlow (ef : EventFlow) : Option FastCauchyWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FastCauchyWitnessUp.mk
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 0 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 1 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 2 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 3 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 4 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 5 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 6 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 7 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 8 ef))
      (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEventAtDefault 9 ef)))

private theorem fastCauchyWitness_round_trip :
    ∀ x : FastCauchyWitnessUp,
      fastCauchyWitnessFromEventFlow (fastCauchyWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D R M E H C P N =>
      change
        some
            (FastCauchyWitnessUp.mk
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist S))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist W))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist D))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist R))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist M))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist E))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist H))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist C))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist P))
              (fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist N))) =
          some (FastCauchyWitnessUp.mk S W D R M E H C P N)
      rw [FastCauchyWitnessTasteGate_single_carrier_alignment_decode S,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode W,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode D,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode R,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode M,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode E,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode H,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode C,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode P,
        FastCauchyWitnessTasteGate_single_carrier_alignment_decode N]

private theorem fastCauchyWitnessToEventFlow_injective
    {x y : FastCauchyWitnessUp} :
    fastCauchyWitnessToEventFlow x = fastCauchyWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastCauchyWitnessFromEventFlow (fastCauchyWitnessToEventFlow x) =
        fastCauchyWitnessFromEventFlow (fastCauchyWitnessToEventFlow y) :=
    congrArg fastCauchyWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastCauchyWitness_round_trip x).symm
      (Eq.trans hread (fastCauchyWitness_round_trip y)))

instance fastCauchyWitnessBHistCarrier : BHistCarrier FastCauchyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchyWitnessToEventFlow
  fromEventFlow := fastCauchyWitnessFromEventFlow

instance fastCauchyWitnessChapterTasteGate : ChapterTasteGate FastCauchyWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastCauchyWitnessFromEventFlow (fastCauchyWitnessToEventFlow x) = some x
    exact fastCauchyWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastCauchyWitnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FastCauchyWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fastCauchyWitnessChapterTasteGate

theorem FastCauchyWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, fastCauchyWitnessDecodeBHist (fastCauchyWitnessEncodeBHist h) = h) ∧
      (∀ x : FastCauchyWitnessUp,
        fastCauchyWitnessFromEventFlow (fastCauchyWitnessToEventFlow x) = some x) ∧
        (∀ x y : FastCauchyWitnessUp,
          fastCauchyWitnessToEventFlow x = fastCauchyWitnessToEventFlow y → x = y) ∧
          fastCauchyWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FastCauchyWitnessTasteGate_single_carrier_alignment_decode,
      fastCauchyWitness_round_trip,
      (fun _ _ heq => fastCauchyWitnessToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FastCauchyWitnessUp
