import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocallyCompactHausdorffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocallyCompactHausdorffUp : Type where
  | mk (T U x V K F S H C P N : BHist) : LocallyCompactHausdorffUp
  deriving DecidableEq

def locallyCompactHausdorffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locallyCompactHausdorffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locallyCompactHausdorffEncodeBHist h

def locallyCompactHausdorffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locallyCompactHausdorffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locallyCompactHausdorffDecodeBHist tail)

private theorem LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locallyCompactHausdorffFields : LocallyCompactHausdorffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocallyCompactHausdorffUp.mk T U x V K F S H C P N =>
      [T, U, x, V, K, F, S, H, C, P, N]

def locallyCompactHausdorffToEventFlow : LocallyCompactHausdorffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | packet => (locallyCompactHausdorffFields packet).map locallyCompactHausdorffEncodeBHist

private def locallyCompactHausdorffEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locallyCompactHausdorffEventAtDefault index rest

def locallyCompactHausdorffFromEventFlow
    (ef : EventFlow) : Option LocallyCompactHausdorffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocallyCompactHausdorffUp.mk
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 0 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 1 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 2 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 3 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 4 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 5 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 6 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 7 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 8 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 9 ef))
      (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEventAtDefault 10 ef)))

private theorem LocallyCompactHausdorffTasteGate_single_carrier_alignment_round_trip
    (packet : LocallyCompactHausdorffUp) :
    locallyCompactHausdorffFromEventFlow
      (locallyCompactHausdorffToEventFlow packet) = some packet := by
  -- BEDC touchpoint anchor: BHist BMark
  cases packet with
  | mk T U x V K F S H C P N =>
      change
        some
          (LocallyCompactHausdorffUp.mk
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist T))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist U))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist x))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist V))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist K))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist F))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist S))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist H))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist C))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist P))
            (locallyCompactHausdorffDecodeBHist (locallyCompactHausdorffEncodeBHist N))) =
          some (LocallyCompactHausdorffUp.mk T U x V K F S H C P N)
      rw [LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode T,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode U,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode x,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode V,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode K,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode F,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode S,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode H,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode C,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode P,
        LocallyCompactHausdorffTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocallyCompactHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocallyCompactHausdorffUp} :
    locallyCompactHausdorffToEventFlow x =
      locallyCompactHausdorffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locallyCompactHausdorffFromEventFlow (locallyCompactHausdorffToEventFlow x) =
        locallyCompactHausdorffFromEventFlow (locallyCompactHausdorffToEventFlow y) :=
    congrArg locallyCompactHausdorffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocallyCompactHausdorffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocallyCompactHausdorffTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocallyCompactHausdorffTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocallyCompactHausdorffUp,
      locallyCompactHausdorffFields x = locallyCompactHausdorffFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ U₁ x₁ V₁ K₁ F₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ U₂ x₂ V₂ K₂ F₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locallyCompactHausdorffBHistCarrier :
    BHistCarrier LocallyCompactHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locallyCompactHausdorffToEventFlow
  fromEventFlow := locallyCompactHausdorffFromEventFlow

instance locallyCompactHausdorffChapterTasteGate :
    ChapterTasteGate LocallyCompactHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro packet
    change
      locallyCompactHausdorffFromEventFlow
        (locallyCompactHausdorffToEventFlow packet) = some packet
    exact LocallyCompactHausdorffTasteGate_single_carrier_alignment_round_trip packet
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocallyCompactHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def LocallyCompactHausdorffTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocallyCompactHausdorffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locallyCompactHausdorffChapterTasteGate

theorem LocallyCompactHausdorffTasteGate_single_carrier_alignment :
    ChapterTasteGate LocallyCompactHausdorffUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact locallyCompactHausdorffChapterTasteGate

end BEDC.Derived.LocallyCompactHausdorffUp
