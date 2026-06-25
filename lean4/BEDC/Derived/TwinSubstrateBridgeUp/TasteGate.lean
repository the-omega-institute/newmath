import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TwinSubstrateBridgeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TwinSubstrateBridgeUp : Type where
  | mk (M G F R L H C P N : BHist) : TwinSubstrateBridgeUp
  deriving DecidableEq

def twinSubstrateBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: twinSubstrateBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: twinSubstrateBridgeEncodeBHist h

def twinSubstrateBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (twinSubstrateBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (twinSubstrateBridgeDecodeBHist tail)

private theorem twinSubstrateBridgeDecode_encode :
    ∀ h : BHist, twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def twinSubstrateBridgeFields : TwinSubstrateBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TwinSubstrateBridgeUp.mk M G F R L H C P N => [M, G, F, R, L, H, C, P, N]

def twinSubstrateBridgeToEventFlow : TwinSubstrateBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (twinSubstrateBridgeFields x).map twinSubstrateBridgeEncodeBHist

private def twinSubstrateBridgeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => twinSubstrateBridgeEventAt index rest

def twinSubstrateBridgeFromEventFlow (ef : EventFlow) : Option TwinSubstrateBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TwinSubstrateBridgeUp.mk
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 0 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 1 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 2 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 3 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 4 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 5 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 6 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 7 ef))
      (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEventAt 8 ef)))

private theorem twinSubstrateBridge_round_trip :
    ∀ x : TwinSubstrateBridgeUp,
      twinSubstrateBridgeFromEventFlow (twinSubstrateBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M G F R L H C P N =>
      change
        some
          (TwinSubstrateBridgeUp.mk
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist M))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist G))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist F))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist R))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist L))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist H))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist C))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist P))
            (twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist N))) =
          some (TwinSubstrateBridgeUp.mk M G F R L H C P N)
      rw [twinSubstrateBridgeDecode_encode M, twinSubstrateBridgeDecode_encode G,
        twinSubstrateBridgeDecode_encode F, twinSubstrateBridgeDecode_encode R,
        twinSubstrateBridgeDecode_encode L, twinSubstrateBridgeDecode_encode H,
        twinSubstrateBridgeDecode_encode C, twinSubstrateBridgeDecode_encode P,
        twinSubstrateBridgeDecode_encode N]

private theorem twinSubstrateBridgeToEventFlow_injective {x y : TwinSubstrateBridgeUp} :
    twinSubstrateBridgeToEventFlow x = twinSubstrateBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      twinSubstrateBridgeFromEventFlow (twinSubstrateBridgeToEventFlow x) =
        twinSubstrateBridgeFromEventFlow (twinSubstrateBridgeToEventFlow y) :=
    congrArg twinSubstrateBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (twinSubstrateBridge_round_trip x).symm
      (Eq.trans hread (twinSubstrateBridge_round_trip y)))

instance twinSubstrateBridgeBHistCarrier : BHistCarrier TwinSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := twinSubstrateBridgeToEventFlow
  fromEventFlow := twinSubstrateBridgeFromEventFlow

instance twinSubstrateBridgeChapterTasteGate : ChapterTasteGate TwinSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change twinSubstrateBridgeFromEventFlow (twinSubstrateBridgeToEventFlow x) = some x
    exact twinSubstrateBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (twinSubstrateBridgeToEventFlow_injective heq)

theorem TwinSubstrateBridgeTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier TwinSubstrateBridgeUp) ∧
      Nonempty (ChapterTasteGate TwinSubstrateBridgeUp) ∧
        (∀ h : BHist, twinSubstrateBridgeDecodeBHist (twinSubstrateBridgeEncodeBHist h) = h) ∧
          (∀ x : TwinSubstrateBridgeUp,
            twinSubstrateBridgeFromEventFlow (twinSubstrateBridgeToEventFlow x) = some x) ∧
            (∀ x y : TwinSubstrateBridgeUp,
              BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) ∧
              twinSubstrateBridgeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  refine
    ⟨⟨twinSubstrateBridgeBHistCarrier⟩,
      ⟨twinSubstrateBridgeChapterTasteGate⟩,
      twinSubstrateBridgeDecode_encode,
      twinSubstrateBridge_round_trip,
      ?_,
      rfl⟩
  intro x y heq
  change twinSubstrateBridgeToEventFlow x = twinSubstrateBridgeToEventFlow y at heq
  exact twinSubstrateBridgeToEventFlow_injective heq

end BEDC.Derived.TwinSubstrateBridgeUp.TasteGate
