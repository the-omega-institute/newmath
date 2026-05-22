import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiEmbeddingUp : Type where
  | mk (M B D T I H C P N : BHist) : KuratowskiEmbeddingUp
  deriving DecidableEq

def kuratowskiEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiEmbeddingEncodeBHist h

def kuratowskiEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiEmbeddingDecodeBHist tail)

private theorem KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiEmbeddingFields : KuratowskiEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiEmbeddingUp.mk M B D T I H C P N => [M, B, D, T, I, H, C, P, N]

def kuratowskiEmbeddingToEventFlow : KuratowskiEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kuratowskiEmbeddingFields x).map kuratowskiEmbeddingEncodeBHist

private def kuratowskiEmbeddingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kuratowskiEmbeddingEventAt index rest

def kuratowskiEmbeddingFromEventFlow (ef : EventFlow) : Option KuratowskiEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KuratowskiEmbeddingUp.mk
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 0 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 1 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 2 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 3 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 4 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 5 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 6 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 7 ef))
      (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEventAt 8 ef)))

private theorem KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_round_trip
    (x : KuratowskiEmbeddingUp) :
    kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M B D T I H C P N =>
      change
        some
          (KuratowskiEmbeddingUp.mk
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist M))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist B))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist D))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist T))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist I))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist H))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist C))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist P))
            (kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist N))) =
          some (KuratowskiEmbeddingUp.mk M B D T I H C P N)
      rw [KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode M,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode B,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode D,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode T,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode I,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode H,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode C,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode P,
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KuratowskiEmbeddingUp} :
    kuratowskiEmbeddingToEventFlow x = kuratowskiEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) =
        kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow y) :=
    congrArg kuratowskiEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_round_trip y)))

instance kuratowskiEmbeddingBHistCarrier : BHistCarrier KuratowskiEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiEmbeddingToEventFlow
  fromEventFlow := kuratowskiEmbeddingFromEventFlow

instance kuratowskiEmbeddingChapterTasteGate : ChapterTasteGate KuratowskiEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) = some x
    exact KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem KuratowskiEmbeddingUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, kuratowskiEmbeddingDecodeBHist (kuratowskiEmbeddingEncodeBHist h) = h) ∧
      (∀ x : KuratowskiEmbeddingUp,
        kuratowskiEmbeddingFromEventFlow (kuratowskiEmbeddingToEventFlow x) = some x) ∧
        (∀ x y : KuratowskiEmbeddingUp,
          kuratowskiEmbeddingToEventFlow x = kuratowskiEmbeddingToEventFlow y → x = y) ∧
          kuratowskiEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_decode_encode,
      KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KuratowskiEmbeddingUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KuratowskiEmbeddingUp
