import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionEndpointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionEndpointUp : Type where
  | mk (B L X U R H C P N : BHist) : RegularCauchyCompletionEndpointUp
  deriving DecidableEq

def regularCauchyCompletionEndpointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionEndpointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionEndpointEncodeBHist h

def regularCauchyCompletionEndpointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionEndpointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionEndpointDecodeBHist tail)

private theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyCompletionEndpointDecodeBHist
        (regularCauchyCompletionEndpointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionEndpointFields :
    RegularCauchyCompletionEndpointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionEndpointUp.mk B L X U R H C P N => [B, L, X, U, R, H, C, P, N]

def regularCauchyCompletionEndpointToEventFlow :
    RegularCauchyCompletionEndpointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyCompletionEndpointEncodeBHist
        (regularCauchyCompletionEndpointFields x)

private def regularCauchyCompletionEndpointEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCompletionEndpointEventAt index rest

def regularCauchyCompletionEndpointFromEventFlow :
    EventFlow → Option RegularCauchyCompletionEndpointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyCompletionEndpointUp.mk
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 0 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 1 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 2 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 3 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 4 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 5 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 6 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 7 ef))
        (regularCauchyCompletionEndpointDecodeBHist
          (regularCauchyCompletionEndpointEventAt 8 ef)))

private theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyCompletionEndpointUp) :
    regularCauchyCompletionEndpointFromEventFlow
      (regularCauchyCompletionEndpointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B L X U R H C P N =>
      change
        some
          (RegularCauchyCompletionEndpointUp.mk
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist B))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist L))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist X))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist U))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist R))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist H))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist C))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist P))
            (regularCauchyCompletionEndpointDecodeBHist
              (regularCauchyCompletionEndpointEncodeBHist N))) =
          some (RegularCauchyCompletionEndpointUp.mk B L X U R H C P N)
      rw [RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode X,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode U,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompletionEndpointUp} :
    regularCauchyCompletionEndpointToEventFlow x =
      regularCauchyCompletionEndpointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionEndpointFromEventFlow
          (regularCauchyCompletionEndpointToEventFlow x) =
        regularCauchyCompletionEndpointFromEventFlow
          (regularCauchyCompletionEndpointToEventFlow y) :=
    congrArg regularCauchyCompletionEndpointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyCompletionEndpointBHistCarrier :
    BHistCarrier RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionEndpointToEventFlow
  fromEventFlow := regularCauchyCompletionEndpointFromEventFlow

instance regularCauchyCompletionEndpointChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionEndpointFromEventFlow
        (regularCauchyCompletionEndpointToEventFlow x) = some x
    exact RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment :
    ChapterTasteGate RegularCauchyCompletionEndpointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionEndpointChapterTasteGate

end BEDC.Derived.RegularCauchyCompletionEndpointUp
