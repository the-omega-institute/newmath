import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PointwiseLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PointwiseLimitUp : Type where
  | mk (X Y F I S Q R E H C K N : BHist) : PointwiseLimitUp
  deriving DecidableEq

def pointwiseLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pointwiseLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pointwiseLimitEncodeBHist h

def pointwiseLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pointwiseLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pointwiseLimitDecodeBHist tail)

private theorem PointwiseLimitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def pointwiseLimitFields : PointwiseLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PointwiseLimitUp.mk X Y F I S Q R E H C K N => [X, Y, F, I, S, Q, R, E, H, C, K, N]

def pointwiseLimitToEventFlow : PointwiseLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (pointwiseLimitFields token).map pointwiseLimitEncodeBHist

private def pointwiseLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pointwiseLimitEventAtDefault index rest

def pointwiseLimitFromEventFlow (ef : EventFlow) : Option PointwiseLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PointwiseLimitUp.mk
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 0 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 1 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 2 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 3 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 4 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 5 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 6 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 7 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 8 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 9 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 10 ef))
      (pointwiseLimitDecodeBHist (pointwiseLimitEventAtDefault 11 ef)))

private theorem PointwiseLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PointwiseLimitUp,
      pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y F I S Q R E H C K N =>
      change
        some
          (PointwiseLimitUp.mk
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist X))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist Y))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist F))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist I))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist S))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist Q))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist R))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist E))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist H))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist C))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist K))
            (pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist N))) =
          some (PointwiseLimitUp.mk X Y F I S Q R E H C K N)
      rw [PointwiseLimitTasteGate_single_carrier_alignment_decode X,
        PointwiseLimitTasteGate_single_carrier_alignment_decode Y,
        PointwiseLimitTasteGate_single_carrier_alignment_decode F,
        PointwiseLimitTasteGate_single_carrier_alignment_decode I,
        PointwiseLimitTasteGate_single_carrier_alignment_decode S,
        PointwiseLimitTasteGate_single_carrier_alignment_decode Q,
        PointwiseLimitTasteGate_single_carrier_alignment_decode R,
        PointwiseLimitTasteGate_single_carrier_alignment_decode E,
        PointwiseLimitTasteGate_single_carrier_alignment_decode H,
        PointwiseLimitTasteGate_single_carrier_alignment_decode C,
        PointwiseLimitTasteGate_single_carrier_alignment_decode K,
        PointwiseLimitTasteGate_single_carrier_alignment_decode N]

private theorem PointwiseLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PointwiseLimitUp} :
    pointwiseLimitToEventFlow x = pointwiseLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) =
        pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow y) :=
    congrArg pointwiseLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PointwiseLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PointwiseLimitTasteGate_single_carrier_alignment_round_trip y)))

instance pointwiseLimitBHistCarrier : BHistCarrier PointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointwiseLimitToEventFlow
  fromEventFlow := pointwiseLimitFromEventFlow

instance pointwiseLimitChapterTasteGate : ChapterTasteGate PointwiseLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) = some x
    exact PointwiseLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PointwiseLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PointwiseLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, pointwiseLimitDecodeBHist (pointwiseLimitEncodeBHist h) = h) ∧
      (∀ x : PointwiseLimitUp,
        pointwiseLimitFromEventFlow (pointwiseLimitToEventFlow x) = some x) ∧
        (∀ x y : PointwiseLimitUp,
          pointwiseLimitToEventFlow x = pointwiseLimitToEventFlow y → x = y) ∧
          pointwiseLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PointwiseLimitTasteGate_single_carrier_alignment_decode,
      PointwiseLimitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PointwiseLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PointwiseLimitUp
