import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionDenseReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionDenseReflectorUp : Type where
  | mk (S I A W T Q R H C P N : BHist) : CauchyCompletionDenseReflectorUp
  deriving DecidableEq

def cauchyCompletionDenseReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionDenseReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionDenseReflectorEncodeBHist h

def cauchyCompletionDenseReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionDenseReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionDenseReflectorDecodeBHist tail)

private theorem CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionDenseReflectorDecodeBHist
        (cauchyCompletionDenseReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionDenseReflectorFields : CauchyCompletionDenseReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionDenseReflectorUp.mk S I A W T Q R H C P N =>
      [S, I, A, W, T, Q, R, H, C, P, N]

def cauchyCompletionDenseReflectorToEventFlow :
    CauchyCompletionDenseReflectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionDenseReflectorFields x).map
      cauchyCompletionDenseReflectorEncodeBHist

private def cauchyCompletionDenseReflectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionDenseReflectorEventAtDefault index rest

def cauchyCompletionDenseReflectorFromEventFlow :
    EventFlow → Option CauchyCompletionDenseReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionDenseReflectorUp.mk
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 0 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 1 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 2 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 3 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 4 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 5 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 6 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 7 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 8 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 9 ef))
        (cauchyCompletionDenseReflectorDecodeBHist
          (cauchyCompletionDenseReflectorEventAtDefault 10 ef)))

private theorem CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionDenseReflectorUp,
      cauchyCompletionDenseReflectorFromEventFlow
        (cauchyCompletionDenseReflectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S I A W T Q R H C P N =>
      change
        some
          (CauchyCompletionDenseReflectorUp.mk
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist S))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist I))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist A))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist W))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist T))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist Q))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist R))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist H))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist C))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist P))
            (cauchyCompletionDenseReflectorDecodeBHist
              (cauchyCompletionDenseReflectorEncodeBHist N))) =
          some (CauchyCompletionDenseReflectorUp.mk S I A W T Q R H C P N)
      rw [CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode I,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode A,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode W,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode T,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode Q,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode R,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionDenseReflectorUp} :
    cauchyCompletionDenseReflectorToEventFlow x =
      cauchyCompletionDenseReflectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionDenseReflectorFromEventFlow
          (cauchyCompletionDenseReflectorToEventFlow x) =
        cauchyCompletionDenseReflectorFromEventFlow
          (cauchyCompletionDenseReflectorToEventFlow y) :=
    congrArg cauchyCompletionDenseReflectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionDenseReflectorBHistCarrier :
    BHistCarrier CauchyCompletionDenseReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionDenseReflectorToEventFlow
  fromEventFlow := cauchyCompletionDenseReflectorFromEventFlow

instance cauchyCompletionDenseReflectorChapterTasteGate :
    ChapterTasteGate CauchyCompletionDenseReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionDenseReflectorFromEventFlow
        (cauchyCompletionDenseReflectorToEventFlow x) = some x
    exact CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate CauchyCompletionDenseReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionDenseReflectorChapterTasteGate

theorem CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionDenseReflectorDecodeBHist
        (cauchyCompletionDenseReflectorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionDenseReflectorUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionDenseReflectorUp) ∧
          cauchyCompletionDenseReflectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionDenseReflectorTasteGate_single_carrier_alignment_decode,
      ⟨cauchyCompletionDenseReflectorBHistCarrier⟩,
      ⟨cauchyCompletionDenseReflectorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionDenseReflectorUp
