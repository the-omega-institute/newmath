import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UrysohnLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UrysohnLemmaUp : Type where
  | mk (N F0 F1 D O0 O1 M Z C S T H K P L : BHist) : UrysohnLemmaUp
  deriving DecidableEq

def urysohnLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: urysohnLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: urysohnLemmaEncodeBHist h

def urysohnLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (urysohnLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (urysohnLemmaDecodeBHist tail)

private theorem UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def urysohnLemmaFields : UrysohnLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UrysohnLemmaUp.mk N F0 F1 D O0 O1 M Z C S T H K P L =>
      [N, F0, F1, D, O0, O1, M, Z, C, S, T, H, K, P, L]

def urysohnLemmaToEventFlow : UrysohnLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (urysohnLemmaFields x).map urysohnLemmaEncodeBHist

private def urysohnLemmaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => urysohnLemmaEventAt index rest

def urysohnLemmaFromEventFlow (ef : EventFlow) : Option UrysohnLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UrysohnLemmaUp.mk
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 0 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 1 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 2 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 3 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 4 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 5 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 6 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 7 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 8 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 9 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 10 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 11 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 12 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 13 ef))
      (urysohnLemmaDecodeBHist (urysohnLemmaEventAt 14 ef)))

private theorem UrysohnLemmaTasteGate_single_carrier_alignment_round_trip
    (x : UrysohnLemmaUp) :
    urysohnLemmaFromEventFlow (urysohnLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk N F0 F1 D O0 O1 M Z C S T H K P L =>
      change
        some
          (UrysohnLemmaUp.mk
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist N))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist F0))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist F1))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist D))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist O0))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist O1))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist M))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist Z))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist C))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist S))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist T))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist H))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist K))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist P))
            (urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist L))) =
          some (UrysohnLemmaUp.mk N F0 F1 D O0 O1 M Z C S T H K P L)
      rw [UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode N,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode F0,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode F1,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode D,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode O0,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode O1,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode M,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode Z,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode C,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode S,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode T,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode H,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode K,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode P,
        UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode L]

private theorem UrysohnLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UrysohnLemmaUp} :
    urysohnLemmaToEventFlow x = urysohnLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      urysohnLemmaFromEventFlow (urysohnLemmaToEventFlow x) =
        urysohnLemmaFromEventFlow (urysohnLemmaToEventFlow y) :=
    congrArg urysohnLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UrysohnLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UrysohnLemmaTasteGate_single_carrier_alignment_round_trip y)))

instance urysohnLemmaBHistCarrier : BHistCarrier UrysohnLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := urysohnLemmaToEventFlow
  fromEventFlow := urysohnLemmaFromEventFlow

instance urysohnLemmaChapterTasteGate : ChapterTasteGate UrysohnLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change urysohnLemmaFromEventFlow (urysohnLemmaToEventFlow x) = some x
    exact UrysohnLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UrysohnLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UrysohnLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, urysohnLemmaDecodeBHist (urysohnLemmaEncodeBHist h) = h) ∧
      (∀ x : UrysohnLemmaUp,
        urysohnLemmaFromEventFlow (urysohnLemmaToEventFlow x) = some x) ∧
        (∀ x y : UrysohnLemmaUp,
          urysohnLemmaToEventFlow x = urysohnLemmaToEventFlow y → x = y) ∧
          urysohnLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UrysohnLemmaTasteGate_single_carrier_alignment_decode_encode,
      UrysohnLemmaTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => UrysohnLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UrysohnLemmaUp
