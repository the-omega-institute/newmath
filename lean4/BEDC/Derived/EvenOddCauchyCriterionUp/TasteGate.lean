import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EvenOddCauchyCriterionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EvenOddCauchyCriterionUp : Type where
  | mk (A B SA SB epsilon M D F R H C P N : BHist) : EvenOddCauchyCriterionUp
  deriving DecidableEq

def EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist h

def EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fields :
    EvenOddCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EvenOddCauchyCriterionUp.mk A B SA SB epsilon M D F R H C P N =>
      [A, B, SA, SB, epsilon, M, D, F, R, H, C, P, N]

def EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow :
    EvenOddCauchyCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fields x).map
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist

private def EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault index rest

def EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option EvenOddCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EvenOddCauchyCriterionUp.mk
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

private theorem EvenOddCauchyCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EvenOddCauchyCriterionUp,
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B SA SB epsilon M D F R H C P N =>
      change
        some
          (EvenOddCauchyCriterionUp.mk
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist A))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist B))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist SA))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist SB))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist epsilon))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist M))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist D))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist F))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist R))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist H))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist C))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist P))
            (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (EvenOddCauchyCriterionUp.mk A B SA SB epsilon M D F R H C P N)
      rw [EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode A,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode B,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode SA,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode SB,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode epsilon,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode M,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode D,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode F,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode R,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode H,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode C,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode P,
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_decode N]

private theorem
    EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EvenOddCauchyCriterionUp} :
    EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x =
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance evenOddCauchyCriterionBHistCarrier :
    BHistCarrier EvenOddCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow

instance evenOddCauchyCriterionChapterTasteGate :
    ChapterTasteGate EvenOddCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      EvenOddCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
        (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact EvenOddCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EvenOddCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem EvenOddCauchyCriterionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier EvenOddCauchyCriterionUp) ∧
      Nonempty (ChapterTasteGate EvenOddCauchyCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨evenOddCauchyCriterionBHistCarrier⟩,
      ⟨evenOddCauchyCriterionChapterTasteGate⟩⟩

end BEDC.Derived.EvenOddCauchyCriterionUp.TasteGate
