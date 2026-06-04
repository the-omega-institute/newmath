import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiHyperspaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiHyperspaceUp : Type where
  | mk (H E U F D S C P M : BHist) : KuratowskiHyperspaceUp
  deriving DecidableEq

def kuratowskiHyperspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiHyperspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiHyperspaceEncodeBHist h

def kuratowskiHyperspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiHyperspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiHyperspaceDecodeBHist tail)

private theorem KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      kuratowskiHyperspaceDecodeBHist (kuratowskiHyperspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiHyperspaceToEventFlow :
    KuratowskiHyperspaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    match x with
    | KuratowskiHyperspaceUp.mk H E U F D S C P M =>
        [kuratowskiHyperspaceEncodeBHist H,
          kuratowskiHyperspaceEncodeBHist E,
          kuratowskiHyperspaceEncodeBHist U,
          kuratowskiHyperspaceEncodeBHist F,
          kuratowskiHyperspaceEncodeBHist D,
          kuratowskiHyperspaceEncodeBHist S,
          kuratowskiHyperspaceEncodeBHist C,
          kuratowskiHyperspaceEncodeBHist P,
          kuratowskiHyperspaceEncodeBHist M]

private def kuratowskiHyperspaceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      kuratowskiHyperspaceEventAtDefault index rest

def kuratowskiHyperspaceFromEventFlow
    (ef : EventFlow) : Option KuratowskiHyperspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KuratowskiHyperspaceUp.mk
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 0 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 1 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 2 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 3 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 4 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 5 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 6 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 7 ef))
      (kuratowskiHyperspaceDecodeBHist
        (kuratowskiHyperspaceEventAtDefault 8 ef)))

private theorem KuratowskiHyperspaceTasteGate_single_carrier_alignment_round_trip
    (x : KuratowskiHyperspaceUp) :
    kuratowskiHyperspaceFromEventFlow
      (kuratowskiHyperspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H E U F D S C P M =>
      change
        some
          (KuratowskiHyperspaceUp.mk
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist H))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist E))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist U))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist F))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist D))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist S))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist C))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist P))
            (kuratowskiHyperspaceDecodeBHist
              (kuratowskiHyperspaceEncodeBHist M))) =
          some (KuratowskiHyperspaceUp.mk H E U F D S C P M)
      rw [KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode H,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode E,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode U,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode F,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode D,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode S,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode C,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode P,
        KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode M]

private theorem KuratowskiHyperspaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KuratowskiHyperspaceUp} :
    kuratowskiHyperspaceToEventFlow x =
      kuratowskiHyperspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiHyperspaceFromEventFlow (kuratowskiHyperspaceToEventFlow x) =
        kuratowskiHyperspaceFromEventFlow (kuratowskiHyperspaceToEventFlow y) :=
    congrArg kuratowskiHyperspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KuratowskiHyperspaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KuratowskiHyperspaceTasteGate_single_carrier_alignment_round_trip y)))

instance kuratowskiHyperspaceBHistCarrier :
    BHistCarrier KuratowskiHyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiHyperspaceToEventFlow
  fromEventFlow := kuratowskiHyperspaceFromEventFlow

instance kuratowskiHyperspaceChapterTasteGate :
    ChapterTasteGate KuratowskiHyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact KuratowskiHyperspaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (KuratowskiHyperspaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem KuratowskiHyperspaceTasteGate_single_carrier_alignment :
    And
      (kuratowskiHyperspaceDecodeBHist (BMark.b0 :: []) =
        BHist.e0 BHist.Empty)
      (And
        (forall h : BHist,
          kuratowskiHyperspaceDecodeBHist
            (kuratowskiHyperspaceEncodeBHist h) = h)
        (forall x : KuratowskiHyperspaceUp,
          kuratowskiHyperspaceFromEventFlow
            (kuratowskiHyperspaceToEventFlow x) = some x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · rfl
  · constructor
    · exact KuratowskiHyperspaceTasteGate_single_carrier_alignment_decode_encode
    · exact KuratowskiHyperspaceTasteGate_single_carrier_alignment_round_trip

end BEDC.Derived.KuratowskiHyperspaceUp
