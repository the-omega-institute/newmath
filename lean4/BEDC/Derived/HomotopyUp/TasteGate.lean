import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HomotopyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HomotopyUp : Type where
  | mk
      (source target deformation interval endpointZero endpointOne classifier provenance :
        BHist) : HomotopyUp
  deriving DecidableEq

def homotopyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: homotopyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: homotopyEncodeBHist h

def homotopyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (homotopyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (homotopyDecodeBHist tail)

private theorem homotopyDecodeEncode :
    ∀ h : BHist, homotopyDecodeBHist (homotopyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def homotopyFields : HomotopyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HomotopyUp.mk source target deformation interval endpointZero endpointOne classifier
      provenance =>
      [source, target, deformation, interval, endpointZero, endpointOne, classifier,
        provenance]

def homotopyToEventFlow : HomotopyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (homotopyFields x).map homotopyEncodeBHist

private def homotopyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => homotopyEventAt index rest

def homotopyFromEventFlow (ef : EventFlow) : Option HomotopyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HomotopyUp.mk
      (homotopyDecodeBHist (homotopyEventAt 0 ef))
      (homotopyDecodeBHist (homotopyEventAt 1 ef))
      (homotopyDecodeBHist (homotopyEventAt 2 ef))
      (homotopyDecodeBHist (homotopyEventAt 3 ef))
      (homotopyDecodeBHist (homotopyEventAt 4 ef))
      (homotopyDecodeBHist (homotopyEventAt 5 ef))
      (homotopyDecodeBHist (homotopyEventAt 6 ef))
      (homotopyDecodeBHist (homotopyEventAt 7 ef)))

private theorem homotopyRoundTrip :
    ∀ x : HomotopyUp, homotopyFromEventFlow (homotopyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target deformation interval endpointZero endpointOne classifier provenance =>
      change
        some
          (HomotopyUp.mk
            (homotopyDecodeBHist (homotopyEncodeBHist source))
            (homotopyDecodeBHist (homotopyEncodeBHist target))
            (homotopyDecodeBHist (homotopyEncodeBHist deformation))
            (homotopyDecodeBHist (homotopyEncodeBHist interval))
            (homotopyDecodeBHist (homotopyEncodeBHist endpointZero))
            (homotopyDecodeBHist (homotopyEncodeBHist endpointOne))
            (homotopyDecodeBHist (homotopyEncodeBHist classifier))
            (homotopyDecodeBHist (homotopyEncodeBHist provenance))) =
          some
            (HomotopyUp.mk source target deformation interval endpointZero endpointOne
              classifier provenance)
      rw [homotopyDecodeEncode source, homotopyDecodeEncode target,
        homotopyDecodeEncode deformation, homotopyDecodeEncode interval,
        homotopyDecodeEncode endpointZero, homotopyDecodeEncode endpointOne,
        homotopyDecodeEncode classifier, homotopyDecodeEncode provenance]

private theorem homotopyToEventFlow_injective {x y : HomotopyUp} :
    homotopyToEventFlow x = homotopyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      homotopyFromEventFlow (homotopyToEventFlow x) =
        homotopyFromEventFlow (homotopyToEventFlow y) :=
    congrArg homotopyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (homotopyRoundTrip x).symm
      (Eq.trans hread (homotopyRoundTrip y)))

instance homotopyBHistCarrier : BHistCarrier HomotopyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := homotopyToEventFlow
  fromEventFlow := homotopyFromEventFlow

instance homotopyChapterTasteGate : ChapterTasteGate HomotopyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change homotopyFromEventFlow (homotopyToEventFlow x) = some x
    exact homotopyRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (homotopyToEventFlow_injective heq)

theorem HomotopyUp_single_carrier_alignment :
    (∀ h : BHist, homotopyDecodeBHist (homotopyEncodeBHist h) = h) ∧
      (∀ x : HomotopyUp, homotopyFromEventFlow (homotopyToEventFlow x) = some x) ∧
        (∀ x y : HomotopyUp, homotopyToEventFlow x = homotopyToEventFlow y → x = y) ∧
          homotopyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact homotopyDecodeEncode
  constructor
  · exact homotopyRoundTrip
  constructor
  · intro x y heq
    exact homotopyToEventFlow_injective heq
  · rfl

theorem HomotopyTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier HomotopyUp) ∧
      Nonempty (ChapterTasteGate HomotopyUp) ∧
        (∀ x : HomotopyUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          (∀ x y : HomotopyUp,
            BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨homotopyBHistCarrier⟩
  constructor
  · exact ⟨homotopyChapterTasteGate⟩
  constructor
  · intro x
    exact ChapterTasteGate.round_trip x
  · intro x y heq
    exact homotopyToEventFlow_injective heq

end BEDC.Derived.HomotopyUp
