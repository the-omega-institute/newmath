import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicSetUp : Type where
  | mk (X D M K Es Eu Ls Lu A H C P N : BHist) : HyperbolicSetUp
  deriving DecidableEq

def HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist h

def HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem HyperbolicSetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
          (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def HyperbolicSetTasteGate_single_carrier_alignment_fields :
    HyperbolicSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicSetUp.mk X D M K Es Eu Ls Lu A H C P N =>
      [X, D, M, K, Es, Eu, Ls, Lu, A, H, C, P, N]

def HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow :
    HyperbolicSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (HyperbolicSetTasteGate_single_carrier_alignment_fields x).map
      HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist

private def HyperbolicSetTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => HyperbolicSetTasteGate_single_carrier_alignment_eventAt index rest

def HyperbolicSetTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option HyperbolicSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicSetUp.mk
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 0 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 1 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 2 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 3 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 4 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 5 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 6 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 7 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 8 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 9 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 10 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 11 ef))
      (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
        (HyperbolicSetTasteGate_single_carrier_alignment_eventAt 12 ef)))

private theorem HyperbolicSetTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicSetUp) :
    HyperbolicSetTasteGate_single_carrier_alignment_fromEventFlow
        (HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X D M K Es Eu Ls Lu A H C P N =>
      change
        some
          (HyperbolicSetUp.mk
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist X))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist D))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist M))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist K))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist Es))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist Eu))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist Ls))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist Lu))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist A))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist H))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist C))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist P))
            (HyperbolicSetTasteGate_single_carrier_alignment_decodeBHist
              (HyperbolicSetTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (HyperbolicSetUp.mk X D M K Es Eu Ls Lu A H C P N)
      rw [HyperbolicSetTasteGate_single_carrier_alignment_decode_encode X,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode D,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode M,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode K,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode Es,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode Eu,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode Ls,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode Lu,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode A,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode H,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode C,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode P,
        HyperbolicSetTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicSetUp} :
    HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow x =
        HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      HyperbolicSetTasteGate_single_carrier_alignment_fromEventFlow
          (HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow x) =
        HyperbolicSetTasteGate_single_carrier_alignment_fromEventFlow
          (HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg HyperbolicSetTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HyperbolicSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HyperbolicSetTasteGate_single_carrier_alignment_round_trip y)))

instance HyperbolicSetTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier HyperbolicSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := HyperbolicSetTasteGate_single_carrier_alignment_fromEventFlow

instance HyperbolicSetTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate HyperbolicSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      HyperbolicSetTasteGate_single_carrier_alignment_fromEventFlow
          (HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact HyperbolicSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def HyperbolicSetTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HyperbolicSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  HyperbolicSetTasteGate_single_carrier_alignment_ChapterTasteGate

theorem HyperbolicSetTasteGate_single_carrier_alignment :
    ChapterTasteGate HyperbolicSetUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact HyperbolicSetTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.HyperbolicSetUp
