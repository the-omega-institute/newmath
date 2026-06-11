import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuousSupNormCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuousSupNormCompletionUp : Type where
  | mk (S U A K F R W L H C P N : BHist) : ContinuousSupNormCompletionUp

def ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist h

def ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fields :
    ContinuousSupNormCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousSupNormCompletionUp.mk S U A K F R W L H C P N =>
      [S, U, A, K, F, R, W, L, H, C, P, N]

def ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow :
    ContinuousSupNormCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fields x).map
      ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist

private def ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault index rest

def ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option ContinuousSupNormCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuousSupNormCompletionUp.mk
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem ContinuousSupNormCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContinuousSupNormCompletionUp,
      ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fromEventFlow
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S U A K F R W L H C P N =>
      change
        some
          (ContinuousSupNormCompletionUp.mk
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist S))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist U))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist A))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist K))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist F))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist R))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist W))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist L))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist H))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist C))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist P))
            (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decodeBHist
              (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ContinuousSupNormCompletionUp.mk S U A K F R W L H C P N)
      rw [ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode S,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode U,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode A,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode K,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode F,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode R,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode W,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode L,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode H,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode C,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode P,
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_decode N]

private theorem ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuousSupNormCompletionUp} :
    ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow x =
      ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance continuousSupNormCompletionBHistCarrier : BHistCarrier ContinuousSupNormCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fromEventFlow

instance continuousSupNormCompletionChapterTasteGate :
    ChapterTasteGate ContinuousSupNormCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ContinuousSupNormCompletionTasteGate_single_carrier_alignment_fromEventFlow
        (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact ContinuousSupNormCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ContinuousSupNormCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ContinuousSupNormCompletionTasteGate_single_carrier_alignment :
    ChapterTasteGate ContinuousSupNormCompletionUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact continuousSupNormCompletionChapterTasteGate

end BEDC.Derived.ContinuousSupNormCompletionUp
