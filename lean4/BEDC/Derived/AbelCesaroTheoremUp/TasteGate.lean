import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelCesaroTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelCesaroTheoremUp : Type where
  | mk (L H D R E K C P N : BHist) : AbelCesaroTheoremUp
  deriving DecidableEq

private def AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist h

private def AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def AbelCesaroTheoremTasteGate_single_carrier_alignment_fields :
    AbelCesaroTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelCesaroTheoremUp.mk L H D R E K C P N => [L, H, D, R, E, K, C, P, N]

private def AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow :
    AbelCesaroTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_fields x).map
        AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist

private def AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt index rest

private def AbelCesaroTheoremTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option AbelCesaroTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelCesaroTheoremUp.mk
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 0 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 1 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 2 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 3 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 4 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 5 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 6 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 7 ef))
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem AbelCesaroTheoremTasteGate_single_carrier_alignment_round_trip
    (x : AbelCesaroTheoremUp) :
    AbelCesaroTheoremTasteGate_single_carrier_alignment_fromEventFlow
      (AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L H D R E K C P N =>
      change
        some
          (AbelCesaroTheoremUp.mk
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist L))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist H))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist D))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist R))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist E))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist K))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist C))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist P))
            (AbelCesaroTheoremTasteGate_single_carrier_alignment_decodeBHist
              (AbelCesaroTheoremTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (AbelCesaroTheoremUp.mk L H D R E K C P N)
      rw [AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode L,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode H,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode D,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode R,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode E,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode K,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode C,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode P,
        AbelCesaroTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelCesaroTheoremUp} :
    AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow x =
      AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      AbelCesaroTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow x) =
        AbelCesaroTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg AbelCesaroTheoremTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AbelCesaroTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelCesaroTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance abelCesaroTheoremBHistCarrier : BHistCarrier AbelCesaroTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := AbelCesaroTheoremTasteGate_single_carrier_alignment_fromEventFlow

instance abelCesaroTheoremChapterTasteGate :
    ChapterTasteGate AbelCesaroTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      AbelCesaroTheoremTasteGate_single_carrier_alignment_fromEventFlow
        (AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact AbelCesaroTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelCesaroTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AbelCesaroTheoremTasteGate_single_carrier_alignment :
    ChapterTasteGate AbelCesaroTheoremUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact abelCesaroTheoremChapterTasteGate

end BEDC.Derived.AbelCesaroTheoremUp
