import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirichletUniformConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirichletUniformConvergenceUp : Type where
  | mk (S B M W R E H C P N : BHist) : DirichletUniformConvergenceUp
  deriving DecidableEq

def dirichletUniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dirichletUniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dirichletUniformConvergenceEncodeBHist h

def dirichletUniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dirichletUniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dirichletUniformConvergenceDecodeBHist tail)

private theorem dirichletUniformConvergence_decode_encode_bhist :
    ∀ h : BHist,
      dirichletUniformConvergenceDecodeBHist
        (dirichletUniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dirichletUniformConvergenceFields : DirichletUniformConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletUniformConvergenceUp.mk S B M W R E H C P N => [S, B, M, W, R, E, H, C, P, N]

def dirichletUniformConvergenceToEventFlow : DirichletUniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dirichletUniformConvergenceFields x).map dirichletUniformConvergenceEncodeBHist

private def dirichletUniformConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dirichletUniformConvergenceEventAt index rest

def dirichletUniformConvergenceFromEventFlow
    (flow : EventFlow) : Option DirichletUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DirichletUniformConvergenceUp.mk
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 0 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 1 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 2 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 3 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 4 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 5 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 6 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 7 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 8 flow))
      (dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEventAt 9 flow)))

private theorem dirichletUniformConvergence_round_trip :
    ∀ x : DirichletUniformConvergenceUp,
      dirichletUniformConvergenceFromEventFlow
        (dirichletUniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B M W R E H C P N =>
      change
        some
          (DirichletUniformConvergenceUp.mk
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist S))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist B))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist M))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist W))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist R))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist E))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist H))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist C))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist P))
            (dirichletUniformConvergenceDecodeBHist
              (dirichletUniformConvergenceEncodeBHist N))) =
          some (DirichletUniformConvergenceUp.mk S B M W R E H C P N)
      rw [dirichletUniformConvergence_decode_encode_bhist S,
        dirichletUniformConvergence_decode_encode_bhist B,
        dirichletUniformConvergence_decode_encode_bhist M,
        dirichletUniformConvergence_decode_encode_bhist W,
        dirichletUniformConvergence_decode_encode_bhist R,
        dirichletUniformConvergence_decode_encode_bhist E,
        dirichletUniformConvergence_decode_encode_bhist H,
        dirichletUniformConvergence_decode_encode_bhist C,
        dirichletUniformConvergence_decode_encode_bhist P,
        dirichletUniformConvergence_decode_encode_bhist N]

private theorem dirichletUniformConvergenceToEventFlow_injective
    {x y : DirichletUniformConvergenceUp} :
    dirichletUniformConvergenceToEventFlow x = dirichletUniformConvergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dirichletUniformConvergenceFromEventFlow (dirichletUniformConvergenceToEventFlow x) =
        dirichletUniformConvergenceFromEventFlow (dirichletUniformConvergenceToEventFlow y) :=
    congrArg dirichletUniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dirichletUniformConvergence_round_trip x).symm
      (Eq.trans hread (dirichletUniformConvergence_round_trip y)))

instance dirichletUniformConvergenceBHistCarrier :
    BHistCarrier DirichletUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dirichletUniformConvergenceToEventFlow
  fromEventFlow := dirichletUniformConvergenceFromEventFlow

instance dirichletUniformConvergenceChapterTasteGate :
    ChapterTasteGate DirichletUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dirichletUniformConvergenceFromEventFlow
        (dirichletUniformConvergenceToEventFlow x) = some x
    exact dirichletUniformConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dirichletUniformConvergenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DirichletUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dirichletUniformConvergenceChapterTasteGate

theorem DirichletUniformConvergenceTasteGate_single_carrier_alignment :
    (forall h : BHist, dirichletUniformConvergenceDecodeBHist (dirichletUniformConvergenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DirichletUniformConvergenceUp) ∧
        Nonempty (ChapterTasteGate DirichletUniformConvergenceUp) ∧
          dirichletUniformConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact dirichletUniformConvergence_decode_encode_bhist
  · constructor
    · exact ⟨dirichletUniformConvergenceBHistCarrier⟩
    · constructor
      · exact ⟨dirichletUniformConvergenceChapterTasteGate⟩
      · rfl

end BEDC.Derived.DirichletUniformConvergenceUp
