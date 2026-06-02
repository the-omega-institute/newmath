import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevTraceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevTraceBoundaryUp : Type where
  | mk (S B T K M X H C P N : BHist) : SobolevTraceBoundaryUp
  deriving DecidableEq

def sobolevTraceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevTraceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevTraceBoundaryEncodeBHist h

def sobolevTraceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevTraceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevTraceBoundaryDecodeBHist tail)

private theorem SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sobolevTraceBoundaryFields : SobolevTraceBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevTraceBoundaryUp.mk S B T K M X H C P N => [S, B, T, K, M, X, H, C, P, N]

def sobolevTraceBoundaryToEventFlow : SobolevTraceBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sobolevTraceBoundaryFields x).map sobolevTraceBoundaryEncodeBHist

private def sobolevTraceBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sobolevTraceBoundaryEventAtDefault index rest

def sobolevTraceBoundaryFromEventFlow (ef : EventFlow) : Option SobolevTraceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SobolevTraceBoundaryUp.mk
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 0 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 1 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 2 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 3 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 4 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 5 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 6 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 7 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 8 ef))
      (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEventAtDefault 9 ef)))

private theorem SobolevTraceBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SobolevTraceBoundaryUp,
      sobolevTraceBoundaryFromEventFlow (sobolevTraceBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B T K M X H C P N =>
      change
        some
          (SobolevTraceBoundaryUp.mk
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist S))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist B))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist T))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist K))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist M))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist X))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist H))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist C))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist P))
            (sobolevTraceBoundaryDecodeBHist (sobolevTraceBoundaryEncodeBHist N))) =
          some (SobolevTraceBoundaryUp.mk S B T K M X H C P N)
      rw [SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode S,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode B,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode T,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode K,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode M,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode X,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode H,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode C,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode P,
        SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem SobolevTraceBoundaryTasteGate_single_carrier_alignment_injective
    {x y : SobolevTraceBoundaryUp} :
    sobolevTraceBoundaryToEventFlow x = sobolevTraceBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevTraceBoundaryFromEventFlow (sobolevTraceBoundaryToEventFlow x) =
        sobolevTraceBoundaryFromEventFlow (sobolevTraceBoundaryToEventFlow y) :=
    congrArg sobolevTraceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SobolevTraceBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SobolevTraceBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance sobolevTraceBoundaryBHistCarrier :
    BHistCarrier SobolevTraceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevTraceBoundaryToEventFlow
  fromEventFlow := sobolevTraceBoundaryFromEventFlow

instance sobolevTraceBoundaryChapterTasteGate :
    ChapterTasteGate SobolevTraceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sobolevTraceBoundaryFromEventFlow (sobolevTraceBoundaryToEventFlow x) = some x
    exact SobolevTraceBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SobolevTraceBoundaryTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SobolevTraceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sobolevTraceBoundaryChapterTasteGate

theorem SobolevTraceBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, sobolevTraceBoundaryDecodeBHist
      (sobolevTraceBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SobolevTraceBoundaryUp) ∧
        Nonempty (ChapterTasteGate SobolevTraceBoundaryUp) ∧
          sobolevTraceBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨SobolevTraceBoundaryTasteGate_single_carrier_alignment_decode,
      ⟨sobolevTraceBoundaryBHistCarrier⟩,
      ⟨sobolevTraceBoundaryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SobolevTraceBoundaryUp
