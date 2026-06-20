import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectorTriangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectorTriangleUp : Type where
  | mk (B R U M D S Q E H C P N : BHist) : CauchyCompletionReflectorTriangleUp
  deriving DecidableEq

def cauchyCompletionReflectorTriangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectorTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectorTriangleEncodeBHist h

def cauchyCompletionReflectorTriangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectorTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectorTriangleDecodeBHist tail)

private theorem CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectorTriangleFields :
    CauchyCompletionReflectorTriangleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectorTriangleUp.mk B R U M D S Q E H C P N =>
      [B, R, U, M, D, S, Q, E, H, C, P, N]

def cauchyCompletionReflectorTriangleToEventFlow :
    CauchyCompletionReflectorTriangleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionReflectorTriangleFields x).map
      cauchyCompletionReflectorTriangleEncodeBHist

private def cauchyCompletionReflectorTriangleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionReflectorTriangleEventAtDefault index rest

def cauchyCompletionReflectorTriangleFromEventFlow :
    EventFlow → Option CauchyCompletionReflectorTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionReflectorTriangleUp.mk
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 0 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 1 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 2 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 3 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 4 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 5 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 6 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 7 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 8 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 9 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 10 ef))
        (cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEventAtDefault 11 ef)))

private theorem CauchyCompletionReflectorTriangleUp_single_carrier_alignment_round_trip
    (x : CauchyCompletionReflectorTriangleUp) :
    cauchyCompletionReflectorTriangleFromEventFlow
        (cauchyCompletionReflectorTriangleToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B R U M D S Q E H C P N =>
      change
        some
          (CauchyCompletionReflectorTriangleUp.mk
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist B))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist R))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist U))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist M))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist D))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist S))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist Q))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist E))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist H))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist C))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist P))
            (cauchyCompletionReflectorTriangleDecodeBHist
              (cauchyCompletionReflectorTriangleEncodeBHist N))) =
          some (CauchyCompletionReflectorTriangleUp.mk B R U M D S Q E H C P N)
      rw [CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode B,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode R,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode U,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode M,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode D,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode S,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode Q,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode E,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode H,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode C,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode P,
        CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionReflectorTriangleUp_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionReflectorTriangleUp} :
    cauchyCompletionReflectorTriangleToEventFlow x =
        cauchyCompletionReflectorTriangleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          cauchyCompletionReflectorTriangleFromEventFlow
            (cauchyCompletionReflectorTriangleToEventFlow x) :=
        (CauchyCompletionReflectorTriangleUp_single_carrier_alignment_round_trip x).symm
      _ =
          cauchyCompletionReflectorTriangleFromEventFlow
            (cauchyCompletionReflectorTriangleToEventFlow y) :=
        congrArg cauchyCompletionReflectorTriangleFromEventFlow hxy
      _ = some y := CauchyCompletionReflectorTriangleUp_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance cauchyCompletionReflectorTriangleBHistCarrier :
    BHistCarrier CauchyCompletionReflectorTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectorTriangleToEventFlow
  fromEventFlow := cauchyCompletionReflectorTriangleFromEventFlow

instance cauchyCompletionReflectorTriangleChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectorTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectorTriangleFromEventFlow
          (cauchyCompletionReflectorTriangleToEventFlow x) =
        some x
    exact CauchyCompletionReflectorTriangleUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionReflectorTriangleUp_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyCompletionReflectorTriangleUp_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionReflectorTriangleDecodeBHist
          (cauchyCompletionReflectorTriangleEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CauchyCompletionReflectorTriangleUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionReflectorTriangleUp) ∧
          cauchyCompletionReflectorTriangleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionReflectorTriangleUp_single_carrier_alignment_decode_encode,
      ⟨cauchyCompletionReflectorTriangleBHistCarrier⟩,
      ⟨cauchyCompletionReflectorTriangleChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionReflectorTriangleUp
