import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.JacobiIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive JacobiIterationUp : Type where
  | mk (A D R S B H C P N : BHist) : JacobiIterationUp
  deriving DecidableEq

def jacobiIterationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: jacobiIterationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: jacobiIterationEncodeBHist h

def jacobiIterationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (jacobiIterationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (jacobiIterationDecodeBHist tail)

private theorem JacobiIterationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, jacobiIterationDecodeBHist (jacobiIterationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def jacobiIterationFields : JacobiIterationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | JacobiIterationUp.mk A D R S B H C P N => [A, D, R, S, B, H, C, P, N]

def jacobiIterationToEventFlow : JacobiIterationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (jacobiIterationFields x).map jacobiIterationEncodeBHist

private def jacobiIterationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => jacobiIterationEventAtDefault index rest

def jacobiIterationFromEventFlow (ef : EventFlow) : Option JacobiIterationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (JacobiIterationUp.mk
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 0 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 1 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 2 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 3 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 4 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 5 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 6 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 7 ef))
      (jacobiIterationDecodeBHist (jacobiIterationEventAtDefault 8 ef)))

private theorem JacobiIterationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : JacobiIterationUp,
      jacobiIterationFromEventFlow (jacobiIterationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D R S B H C P N =>
      change
        some
          (JacobiIterationUp.mk
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist A))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist D))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist R))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist S))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist B))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist H))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist C))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist P))
            (jacobiIterationDecodeBHist (jacobiIterationEncodeBHist N))) =
          some (JacobiIterationUp.mk A D R S B H C P N)
      rw [JacobiIterationTasteGate_single_carrier_alignment_decode A,
        JacobiIterationTasteGate_single_carrier_alignment_decode D,
        JacobiIterationTasteGate_single_carrier_alignment_decode R,
        JacobiIterationTasteGate_single_carrier_alignment_decode S,
        JacobiIterationTasteGate_single_carrier_alignment_decode B,
        JacobiIterationTasteGate_single_carrier_alignment_decode H,
        JacobiIterationTasteGate_single_carrier_alignment_decode C,
        JacobiIterationTasteGate_single_carrier_alignment_decode P,
        JacobiIterationTasteGate_single_carrier_alignment_decode N]

private theorem JacobiIterationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : JacobiIterationUp} :
    jacobiIterationToEventFlow x = jacobiIterationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      jacobiIterationFromEventFlow (jacobiIterationToEventFlow x) =
        jacobiIterationFromEventFlow (jacobiIterationToEventFlow y) :=
    congrArg jacobiIterationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (JacobiIterationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (JacobiIterationTasteGate_single_carrier_alignment_round_trip y)))

instance jacobiIterationBHistCarrier : BHistCarrier JacobiIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := jacobiIterationToEventFlow
  fromEventFlow := jacobiIterationFromEventFlow

instance jacobiIterationChapterTasteGate : ChapterTasteGate JacobiIterationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change jacobiIterationFromEventFlow (jacobiIterationToEventFlow x) = some x
    exact JacobiIterationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (JacobiIterationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem JacobiIterationTasteGate_single_carrier_alignment :
    (∀ h : BHist, jacobiIterationDecodeBHist (jacobiIterationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier JacobiIterationUp) ∧
        Nonempty (ChapterTasteGate JacobiIterationUp) ∧
          jacobiIterationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨JacobiIterationTasteGate_single_carrier_alignment_decode,
      ⟨⟨jacobiIterationBHistCarrier⟩, ⟨jacobiIterationChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.JacobiIterationUp
