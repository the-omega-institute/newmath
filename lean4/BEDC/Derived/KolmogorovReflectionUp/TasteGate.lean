import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KolmogorovReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KolmogorovReflectionUp : Type where
  | mk (X T M S R H C P N : BHist) : KolmogorovReflectionUp
  deriving DecidableEq

def KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist h

def KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
        (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def KolmogorovReflectionTasteGate_single_carrier_alignment_fields :
    KolmogorovReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KolmogorovReflectionUp.mk X T M S R H C P N => [X, T, M, S, R, H, C, P, N]

def KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow :
    KolmogorovReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (KolmogorovReflectionTasteGate_single_carrier_alignment_fields x).map
        KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist

private def KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt index rest

def KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option KolmogorovReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (KolmogorovReflectionUp.mk
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 0 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 1 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 2 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 3 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 4 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 5 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 6 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 7 ef))
        (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
          (KolmogorovReflectionTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem KolmogorovReflectionTasteGate_single_carrier_alignment_round_trip
    (x : KolmogorovReflectionUp) :
    KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow
        (KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X T M S R H C P N =>
      change
        some
          (KolmogorovReflectionUp.mk
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist X))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist T))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist M))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist S))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist R))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist H))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist C))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist P))
            (KolmogorovReflectionTasteGate_single_carrier_alignment_decodeBHist
              (KolmogorovReflectionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (KolmogorovReflectionUp.mk X T M S R H C P N)
      rw [KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode X,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode T,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode M,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode S,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode R,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode H,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode C,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode P,
        KolmogorovReflectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KolmogorovReflectionUp} :
    KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow x =
        KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow
          (KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow x) =
        KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow
          (KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KolmogorovReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KolmogorovReflectionTasteGate_single_carrier_alignment_round_trip y)))

instance kolmogorovReflectionBHistCarrier : BHistCarrier KolmogorovReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow

instance kolmogorovReflectionChapterTasteGate :
    ChapterTasteGate KolmogorovReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow
          (KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact KolmogorovReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem KolmogorovReflectionTasteGate_single_carrier_alignment :
    ChapterTasteGate KolmogorovReflectionUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      KolmogorovReflectionTasteGate_single_carrier_alignment_fromEventFlow
          (KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact KolmogorovReflectionTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy (KolmogorovReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

end BEDC.Derived.KolmogorovReflectionUp
