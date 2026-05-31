import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AsymptoticEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AsymptoticEquivalenceUp : Type where
  | mk (sourceLeft sourceRight readbackLeft readbackRight dyadicLedger tailWindows realSeal
      transport replay provenance localName : BHist) : AsymptoticEquivalenceUp
  deriving DecidableEq

def asymptoticEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: asymptoticEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: asymptoticEquivalenceEncodeBHist h

def asymptoticEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (asymptoticEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (asymptoticEquivalenceDecodeBHist tail)

private theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def asymptoticEquivalenceFields : AsymptoticEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AsymptoticEquivalenceUp.mk sourceLeft sourceRight readbackLeft readbackRight dyadicLedger
      tailWindows realSeal transport replay provenance localName =>
      [sourceLeft, sourceRight, readbackLeft, readbackRight, dyadicLedger, tailWindows, realSeal,
        transport, replay, provenance, localName]

def asymptoticEquivalenceToEventFlow : AsymptoticEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (asymptoticEquivalenceFields x).map asymptoticEquivalenceEncodeBHist

private def asymptoticEquivalenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => asymptoticEquivalenceEventAt index rest

def asymptoticEquivalenceFromEventFlow (ef : EventFlow) :
    Option AsymptoticEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AsymptoticEquivalenceUp.mk
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 0 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 1 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 2 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 3 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 4 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 5 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 6 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 7 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 8 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 9 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 10 ef)))

def asymptoticEquivalenceBHistCarrier :
    BHistCarrier AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := asymptoticEquivalenceToEventFlow
  fromEventFlow := asymptoticEquivalenceFromEventFlow

instance asymptoticEquivalenceBHistCarrierInstance :
    BHistCarrier AsymptoticEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  asymptoticEquivalenceBHistCarrier

private theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip
    (x : AsymptoticEquivalenceUp) :
    asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk sourceLeft sourceRight readbackLeft readbackRight dyadicLedger tailWindows realSeal
      transport replay provenance localName =>
      change
        some
          (AsymptoticEquivalenceUp.mk
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist sourceLeft))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist sourceRight))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist readbackLeft))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist readbackRight))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist dyadicLedger))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist tailWindows))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist realSeal))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist transport))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist replay))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist provenance))
            (asymptoticEquivalenceDecodeBHist
              (asymptoticEquivalenceEncodeBHist localName))) =
          some
            (AsymptoticEquivalenceUp.mk sourceLeft sourceRight readbackLeft readbackRight
              dyadicLedger tailWindows realSeal transport replay provenance localName)
      rw [AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode sourceLeft,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode sourceRight,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode readbackLeft,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode readbackRight,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode tailWindows,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode realSeal,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode transport,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode replay,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode provenance,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AsymptoticEquivalenceUp} :
    asymptoticEquivalenceToEventFlow x = asymptoticEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) =
        asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow y) :=
    congrArg asymptoticEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

def asymptoticEquivalenceChapterTasteGate :
    @ChapterTasteGate AsymptoticEquivalenceUp asymptoticEquivalenceBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AsymptoticEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance asymptoticEquivalenceChapterTasteGateInstance :
    ChapterTasteGate AsymptoticEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  asymptoticEquivalenceChapterTasteGate

theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier AsymptoticEquivalenceUp) ∧
      Nonempty (ChapterTasteGate AsymptoticEquivalenceUp) ∧
      asymptoticEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨asymptoticEquivalenceBHistCarrier⟩,
        ⟨⟨asymptoticEquivalenceChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.AsymptoticEquivalenceUp
