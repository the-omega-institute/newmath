import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CevaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CevaUp : Type where
  | mk (T S L X H C P N : BHist) : CevaUp
  deriving DecidableEq

def cevaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cevaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cevaEncodeBHist h

def cevaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cevaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cevaDecodeBHist tail)

private theorem CevaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cevaDecodeBHist (cevaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cevaFields : CevaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CevaUp.mk T S L X H C P N => [T, S, L, X, H, C, P, N]

def cevaToEventFlow : CevaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cevaFields x).map cevaEncodeBHist

private def cevaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cevaEventAt index rest

def cevaFromEventFlow (ef : EventFlow) : Option CevaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CevaUp.mk
      (cevaDecodeBHist (cevaEventAt 0 ef))
      (cevaDecodeBHist (cevaEventAt 1 ef))
      (cevaDecodeBHist (cevaEventAt 2 ef))
      (cevaDecodeBHist (cevaEventAt 3 ef))
      (cevaDecodeBHist (cevaEventAt 4 ef))
      (cevaDecodeBHist (cevaEventAt 5 ef))
      (cevaDecodeBHist (cevaEventAt 6 ef))
      (cevaDecodeBHist (cevaEventAt 7 ef)))

private theorem CevaTasteGate_single_carrier_alignment_round_trip
    (x : CevaUp) :
    cevaFromEventFlow (cevaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T S L X H C P N =>
      change
        some
          (CevaUp.mk
            (cevaDecodeBHist (cevaEncodeBHist T))
            (cevaDecodeBHist (cevaEncodeBHist S))
            (cevaDecodeBHist (cevaEncodeBHist L))
            (cevaDecodeBHist (cevaEncodeBHist X))
            (cevaDecodeBHist (cevaEncodeBHist H))
            (cevaDecodeBHist (cevaEncodeBHist C))
            (cevaDecodeBHist (cevaEncodeBHist P))
            (cevaDecodeBHist (cevaEncodeBHist N))) =
          some (CevaUp.mk T S L X H C P N)
      rw [CevaTasteGate_single_carrier_alignment_decode_encode T,
        CevaTasteGate_single_carrier_alignment_decode_encode S,
        CevaTasteGate_single_carrier_alignment_decode_encode L,
        CevaTasteGate_single_carrier_alignment_decode_encode X,
        CevaTasteGate_single_carrier_alignment_decode_encode H,
        CevaTasteGate_single_carrier_alignment_decode_encode C,
        CevaTasteGate_single_carrier_alignment_decode_encode P,
        CevaTasteGate_single_carrier_alignment_decode_encode N]

private theorem CevaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CevaUp} :
    cevaToEventFlow x = cevaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cevaFromEventFlow (cevaToEventFlow x) =
        cevaFromEventFlow (cevaToEventFlow y) :=
    congrArg cevaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CevaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CevaTasteGate_single_carrier_alignment_round_trip y)))

instance cevaBHistCarrier : BHistCarrier CevaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cevaToEventFlow
  fromEventFlow := cevaFromEventFlow

instance cevaChapterTasteGate : ChapterTasteGate CevaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cevaFromEventFlow (cevaToEventFlow x) = some x
    exact CevaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CevaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CevaTasteGate_single_carrier_alignment_taste_gate : ChapterTasteGate CevaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cevaChapterTasteGate

theorem CevaTasteGate_single_carrier_alignment :
    (∀ h : BHist, cevaDecodeBHist (cevaEncodeBHist h) = h) ∧
      (∀ x : CevaUp, cevaFromEventFlow (cevaToEventFlow x) = some x) ∧
        (∀ x y : CevaUp, cevaToEventFlow x = cevaToEventFlow y → x = y) ∧
          cevaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CevaTasteGate_single_carrier_alignment_decode_encode,
      CevaTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CevaTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CevaUp.TasteGate
