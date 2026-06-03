import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyLocatedRealEquivalenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyLocatedRealEquivalenceUp : Type where
  | packet
      (cauchy locatedLower locatedUpper window readback decision equivalence transport
        continuation provenance nameRow : BHist) :
      CauchyLocatedRealEquivalenceUp

def CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist h

def cauchyLocatedRealEquivalenceDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyLocatedRealEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyLocatedRealEquivalenceDecodeBHist tail)

private theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyLocatedRealEquivalenceDecodeBHist
          (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyLocatedRealEquivalenceFields :
    CauchyLocatedRealEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyLocatedRealEquivalenceUp.packet cauchy locatedLower locatedUpper window readback
      decision equivalence transport continuation provenance nameRow =>
      [cauchy, locatedLower, locatedUpper, window, readback, decision, equivalence,
        transport, continuation, provenance, nameRow]

def cauchyLocatedRealEquivalenceToEventFlow :
    CauchyLocatedRealEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyLocatedRealEquivalenceFields x).map
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist

private def cauchyLocatedRealEquivalenceRawAt : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, raw :: _ => raw
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => cauchyLocatedRealEquivalenceRawAt index rest

def cauchyLocatedRealEquivalenceFromEventFlow
    (flow : EventFlow) : Option CauchyLocatedRealEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyLocatedRealEquivalenceUp.packet
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 0 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 1 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 2 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 3 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 4 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 5 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 6 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 7 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 8 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 9 flow))
      (cauchyLocatedRealEquivalenceDecodeBHist
        (cauchyLocatedRealEquivalenceRawAt 10 flow)))

private theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip
    (x : CauchyLocatedRealEquivalenceUp) :
    cauchyLocatedRealEquivalenceFromEventFlow
        (cauchyLocatedRealEquivalenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet cauchy locatedLower locatedUpper window readback decision equivalence transport
      continuation provenance nameRow =>
      change
        some
          (CauchyLocatedRealEquivalenceUp.packet
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                cauchy))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                locatedLower))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                locatedUpper))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                window))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                readback))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                decision))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                equivalence))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                transport))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                continuation))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                provenance))
            (cauchyLocatedRealEquivalenceDecodeBHist
              (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
                nameRow))) =
          some
            (CauchyLocatedRealEquivalenceUp.packet cauchy locatedLower locatedUpper window
              readback decision equivalence transport continuation provenance nameRow)
      rw [CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode cauchy,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode
          locatedLower,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode
          locatedUpper,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode window,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode readback,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode decision,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode
          equivalence,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode
          transport,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode
          continuation,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode
          provenance,
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode nameRow]

private theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyLocatedRealEquivalenceUp} :
    cauchyLocatedRealEquivalenceToEventFlow x =
      cauchyLocatedRealEquivalenceToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyLocatedRealEquivalenceFromEventFlow
          (cauchyLocatedRealEquivalenceToEventFlow x) =
        cauchyLocatedRealEquivalenceFromEventFlow
          (cauchyLocatedRealEquivalenceToEventFlow y) :=
    congrArg cauchyLocatedRealEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyLocatedRealEquivalenceBHistCarrier :
    BHistCarrier CauchyLocatedRealEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyLocatedRealEquivalenceToEventFlow
  fromEventFlow := cauchyLocatedRealEquivalenceFromEventFlow

instance cauchyLocatedRealEquivalenceChapterTasteGate :
    ChapterTasteGate CauchyLocatedRealEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyLocatedRealEquivalenceFromEventFlow
          (cauchyLocatedRealEquivalenceToEventFlow x) =
        some x
    exact CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate CauchyLocatedRealEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyLocatedRealEquivalenceChapterTasteGate

theorem CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyLocatedRealEquivalenceDecodeBHist
          (CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      (∀ x : CauchyLocatedRealEquivalenceUp,
        cauchyLocatedRealEquivalenceFromEventFlow
            (cauchyLocatedRealEquivalenceToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyLocatedRealEquivalenceUp,
          cauchyLocatedRealEquivalenceToEventFlow x =
            cauchyLocatedRealEquivalenceToEventFlow y →
          x = y) ∧
          CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_encodeBHist
            BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_decode_encode,
      CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyLocatedRealEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.CauchyLocatedRealEquivalenceUp.TasteGate
