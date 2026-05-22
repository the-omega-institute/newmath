import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KreiselLacombeShoenfieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KreiselLacombeShoenfieldUp : Type where
  | mk (B O S R E M L H C P N : BHist) : KreiselLacombeShoenfieldUp
  deriving DecidableEq

def kreiselLacombeShoenfieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kreiselLacombeShoenfieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kreiselLacombeShoenfieldEncodeBHist h

def kreiselLacombeShoenfieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kreiselLacombeShoenfieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kreiselLacombeShoenfieldDecodeBHist tail)

private theorem KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def kreiselLacombeShoenfieldToEventFlow :
    KreiselLacombeShoenfieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KreiselLacombeShoenfieldUp.mk B O S R E M L H C P N =>
      [kreiselLacombeShoenfieldEncodeBHist B,
        kreiselLacombeShoenfieldEncodeBHist O,
        kreiselLacombeShoenfieldEncodeBHist S,
        kreiselLacombeShoenfieldEncodeBHist R,
        kreiselLacombeShoenfieldEncodeBHist E,
        kreiselLacombeShoenfieldEncodeBHist M,
        kreiselLacombeShoenfieldEncodeBHist L,
        kreiselLacombeShoenfieldEncodeBHist H,
        kreiselLacombeShoenfieldEncodeBHist C,
        kreiselLacombeShoenfieldEncodeBHist P,
        kreiselLacombeShoenfieldEncodeBHist N]

private def kreiselLacombeShoenfieldEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kreiselLacombeShoenfieldEventAt index rest

def kreiselLacombeShoenfieldFromEventFlow :
    EventFlow → Option KreiselLacombeShoenfieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (KreiselLacombeShoenfieldUp.mk
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 0 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 1 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 2 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 3 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 4 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 5 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 6 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 7 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 8 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 9 ef))
        (kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEventAt 10 ef)))

private theorem KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_round_trip
    (x : KreiselLacombeShoenfieldUp) :
    kreiselLacombeShoenfieldFromEventFlow (kreiselLacombeShoenfieldToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B O S R E M L H C P N =>
      change
        some
          (KreiselLacombeShoenfieldUp.mk
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist B))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist O))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist S))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist R))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist E))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist M))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist L))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist H))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist C))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist P))
            (kreiselLacombeShoenfieldDecodeBHist
              (kreiselLacombeShoenfieldEncodeBHist N))) =
          some (KreiselLacombeShoenfieldUp.mk B O S R E M L H C P N)
      rw [KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode B,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode O,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode S,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode R,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode E,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode M,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode L,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode H,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode C,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode P,
        KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode N]

private theorem KreiselLacombeShoenfieldToEventFlow_injective
    {x y : KreiselLacombeShoenfieldUp} :
    kreiselLacombeShoenfieldToEventFlow x = kreiselLacombeShoenfieldToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kreiselLacombeShoenfieldFromEventFlow (kreiselLacombeShoenfieldToEventFlow x) =
        kreiselLacombeShoenfieldFromEventFlow (kreiselLacombeShoenfieldToEventFlow y) :=
    congrArg kreiselLacombeShoenfieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_round_trip y)))

instance kreiselLacombeShoenfieldBHistCarrier :
    BHistCarrier KreiselLacombeShoenfieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kreiselLacombeShoenfieldToEventFlow
  fromEventFlow := kreiselLacombeShoenfieldFromEventFlow

instance kreiselLacombeShoenfieldChapterTasteGate :
    ChapterTasteGate KreiselLacombeShoenfieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kreiselLacombeShoenfieldFromEventFlow
          (kreiselLacombeShoenfieldToEventFlow x) =
        some x
    exact KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KreiselLacombeShoenfieldToEventFlow_injective heq)

def KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate KreiselLacombeShoenfieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kreiselLacombeShoenfieldChapterTasteGate

theorem KreiselLacombeShoenfieldTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kreiselLacombeShoenfieldDecodeBHist (kreiselLacombeShoenfieldEncodeBHist h) = h) ∧
      (∀ x : KreiselLacombeShoenfieldUp,
        kreiselLacombeShoenfieldFromEventFlow
            (kreiselLacombeShoenfieldToEventFlow x) =
          some x) ∧
        (∀ x y : KreiselLacombeShoenfieldUp,
          kreiselLacombeShoenfieldToEventFlow x =
              kreiselLacombeShoenfieldToEventFlow y →
            x = y) ∧
          kreiselLacombeShoenfieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_decode,
      KreiselLacombeShoenfieldTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => KreiselLacombeShoenfieldToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KreiselLacombeShoenfieldUp
