import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleeneKreiselContinuousFunctionalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleeneKreiselContinuousFunctionalUp : Type where
  | mk (S C F Nb Sc H T P N : BHist) : KleeneKreiselContinuousFunctionalUp

def KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist h

def KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
        (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fields :
    KleeneKreiselContinuousFunctionalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleeneKreiselContinuousFunctionalUp.mk S C F Nb Sc H T P N => [S, C, F, Nb, Sc, H, T, P, N]

def KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow :
    KleeneKreiselContinuousFunctionalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fields x).map
      KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist

def KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option KleeneKreiselContinuousFunctionalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, C, F, Nb, Sc, H, T, P, N] =>
      some
        (KleeneKreiselContinuousFunctionalUp.mk
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist S)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist C)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist F)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist Nb)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist Sc)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist H)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist T)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist P)
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_round_trip
    (x : KleeneKreiselContinuousFunctionalUp) :
    KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fromEventFlow
      (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S C F Nb Sc H T P N =>
      change
        some
          (KleeneKreiselContinuousFunctionalUp.mk
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist S))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist C))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist F))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist Nb))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist Sc))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist H))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist T))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist P))
            (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decodeBHist
              (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (KleeneKreiselContinuousFunctionalUp.mk S C F Nb Sc H T P N)
      rw [KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode S,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode C,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode F,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode Nb,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode Sc,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode H,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode T,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode P,
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_decode_encode N]

private theorem KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KleeneKreiselContinuousFunctionalUp} :
    KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow x =
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fromEventFlow
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow x) =
        KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fromEventFlow
          (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_round_trip y)))

instance kleeneKreiselContinuousFunctionalBHistCarrier :
    BHistCarrier KleeneKreiselContinuousFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fromEventFlow

instance kleeneKreiselContinuousFunctionalChapterTasteGate :
    ChapterTasteGate KleeneKreiselContinuousFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_fromEventFlow
        (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
    exact KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate KleeneKreiselContinuousFunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kleeneKreiselContinuousFunctionalChapterTasteGate

theorem KleeneKreiselContinuousFunctionalTasteGate_single_carrier_alignment :
    ChapterTasteGate KleeneKreiselContinuousFunctionalUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact taste_gate

end BEDC.Derived.KleeneKreiselContinuousFunctionalUp
