import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CodonLiftOrbitClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CodonLiftOrbitClassifierUp : Type where
  | mk (A E Gamma T B K H C P N : BHist) : CodonLiftOrbitClassifierUp
  deriving DecidableEq

def CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist h

def CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
          (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fields :
    CodonLiftOrbitClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CodonLiftOrbitClassifierUp.mk A E Gamma T B K H C P N =>
      [A, E, Gamma, T, B, K, H, C, P, N]

def CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow :
    CodonLiftOrbitClassifierUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fields x).map
      CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist

private def CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt index rest

def CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CodonLiftOrbitClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CodonLiftOrbitClassifierUp.mk
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 0 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 1 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 2 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 3 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 4 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 5 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 6 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 7 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 8 ef))
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_round_trip
    (x : CodonLiftOrbitClassifierUp) :
    CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A E Gamma T B K H C P N =>
      change
        some
            (CodonLiftOrbitClassifierUp.mk
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist A))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist E))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist Gamma))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist T))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist B))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist K))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist H))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist C))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist P))
              (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decodeBHist
                (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CodonLiftOrbitClassifierUp.mk A E Gamma T B K H C P N)
      rw [CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode A,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode E,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode Gamma,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode T,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode B,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode K,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode H,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode C,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode P,
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_decode_encode N]

private theorem CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CodonLiftOrbitClassifierUp} :
    CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow x =
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow
          (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow x) =
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow
          (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_round_trip y)))

instance codonLiftOrbitClassifierBHistCarrier :
    BHistCarrier CodonLiftOrbitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow

instance codonLiftOrbitClassifierChapterTasteGate :
    ChapterTasteGate CodonLiftOrbitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow
          (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CodonLiftOrbitClassifierTasteGate_single_carrier_alignment :
    ChapterTasteGate CodonLiftOrbitClassifierUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact {
    round_trip := by
      intro x
      change
        CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_fromEventFlow
            (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
      exact CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy
        (CodonLiftOrbitClassifierTasteGate_single_carrier_alignment_toEventFlow_injective heq)
  }

end BEDC.Derived.CodonLiftOrbitClassifierUp
