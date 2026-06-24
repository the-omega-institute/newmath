import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannUniformMeshUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannUniformMeshUp : Type where
  | mk (P D W R S E H C G N : BHist) : RiemannUniformMeshUp
  deriving DecidableEq

def riemannUniformMeshEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannUniformMeshEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannUniformMeshEncodeBHist h

def riemannUniformMeshDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannUniformMeshDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannUniformMeshDecodeBHist tail)

private theorem RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannUniformMeshFields : RiemannUniformMeshUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannUniformMeshUp.mk P D W R S E H C G N => [P, D, W, R, S, E, H, C, G, N]

def riemannUniformMeshToEventFlow : RiemannUniformMeshUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannUniformMeshFields x).map riemannUniformMeshEncodeBHist

private def riemannUniformMeshEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannUniformMeshEventAt index rest

def riemannUniformMeshFromEventFlow (ef : EventFlow) : Option RiemannUniformMeshUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannUniformMeshUp.mk
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 0 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 1 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 2 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 3 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 4 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 5 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 6 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 7 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 8 ef))
      (riemannUniformMeshDecodeBHist (riemannUniformMeshEventAt 9 ef)))

private theorem RiemannUniformMeshTasteGate_single_carrier_alignment_round_trip
    (x : RiemannUniformMeshUp) :
    riemannUniformMeshFromEventFlow (riemannUniformMeshToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P D W R S E H C G N =>
      change
        some
          (RiemannUniformMeshUp.mk
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist P))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist D))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist W))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist R))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist S))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist E))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist H))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist C))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist G))
            (riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist N))) =
          some (RiemannUniformMeshUp.mk P D W R S E H C G N)
      rw [RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode P,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode D,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode W,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode R,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode S,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode E,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode H,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode C,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode G,
        RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannUniformMeshTasteGate_single_carrier_alignment_injective
    {x y : RiemannUniformMeshUp} :
    riemannUniformMeshToEventFlow x = riemannUniformMeshToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannUniformMeshFromEventFlow (riemannUniformMeshToEventFlow x) =
        riemannUniformMeshFromEventFlow (riemannUniformMeshToEventFlow y) :=
    congrArg riemannUniformMeshFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannUniformMeshTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannUniformMeshTasteGate_single_carrier_alignment_round_trip y)))

instance riemannUniformMeshBHistCarrier : BHistCarrier RiemannUniformMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannUniformMeshToEventFlow
  fromEventFlow := riemannUniformMeshFromEventFlow

instance riemannUniformMeshChapterTasteGate : ChapterTasteGate RiemannUniformMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannUniformMeshFromEventFlow (riemannUniformMeshToEventFlow x) = some x
    exact RiemannUniformMeshTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannUniformMeshTasteGate_single_carrier_alignment_injective heq)

theorem RiemannUniformMeshTasteGate_single_carrier_alignment :
    (∀ h : BHist, riemannUniformMeshDecodeBHist (riemannUniformMeshEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RiemannUniformMeshUp) ∧
        Nonempty (ChapterTasteGate RiemannUniformMeshUp) ∧
          riemannUniformMeshEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RiemannUniformMeshTasteGate_single_carrier_alignment_decode_encode,
      ⟨riemannUniformMeshBHistCarrier⟩, ⟨riemannUniformMeshChapterTasteGate⟩, rfl⟩

end BEDC.Derived.RiemannUniformMeshUp
