import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyStructureUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyStructureUp : Type where
  | mk (F G D S R E H C P N : BHist) : CauchyStructureUp
  deriving DecidableEq

def CauchyStructureTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyStructureTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyStructureTasteGate_single_carrier_alignment_encodeBHist h

def CauchyStructureTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyStructureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CauchyStructureTasteGate_single_carrier_alignment_fields : CauchyStructureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyStructureUp.mk F G D S R E H C P N => [F, G, D, S, R, E, H, C, P, N]

def CauchyStructureTasteGate_single_carrier_alignment_toEventFlow : CauchyStructureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (CauchyStructureTasteGate_single_carrier_alignment_fields token).map CauchyStructureTasteGate_single_carrier_alignment_encodeBHist

private def CauchyStructureTasteGate_single_carrier_alignment_rawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyStructureTasteGate_single_carrier_alignment_rawAt index rest

private def CauchyStructureTasteGate_single_carrier_alignment_lengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest =>
      CauchyStructureTasteGate_single_carrier_alignment_lengthEq n rest

def CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow : EventFlow → Option CauchyStructureUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match CauchyStructureTasteGate_single_carrier_alignment_lengthEq 10 flow with
      | true =>
          some
            (CauchyStructureUp.mk
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 0 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 1 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 2 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 3 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 4 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 5 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 6 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 7 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 8 flow))
              (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
                (CauchyStructureTasteGate_single_carrier_alignment_rawAt 9 flow)))
      | false => none

private theorem CauchyStructureTasteGate_single_carrier_alignment_round_trip :
    ∀ token : CauchyStructureUp,
      CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F G D S R E H C P N =>
      change
        some
          (CauchyStructureUp.mk
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist F))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist G))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist S))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist R))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist E))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist H))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyStructureTasteGate_single_carrier_alignment_decodeBHist (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyStructureUp.mk F G D S R E H C P N)
      rw [CauchyStructureTasteGate_single_carrier_alignment_decode_encode F,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode G,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode D,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode S,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode R,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode E,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode H,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode C,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode P,
        CauchyStructureTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyStructureTasteGate_single_carrier_alignment_toEventFlow_injective {x y : CauchyStructureUp} :
    CauchyStructureTasteGate_single_carrier_alignment_toEventFlow x = CauchyStructureTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyStructureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyStructureTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyStructureBHistCarrier : BHistCarrier CauchyStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyStructureTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow

instance cauchyStructureChapterTasteGate : ChapterTasteGate CauchyStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact CauchyStructureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyStructureTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CauchyStructureTasteGate_single_carrier_alignment_decodeBHist
          (CauchyStructureTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      (∀ x : CauchyStructureUp,
        CauchyStructureTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyStructureTasteGate_single_carrier_alignment_toEventFlow x) =
          some x) ∧
      CauchyStructureTasteGate_single_carrier_alignment_encodeBHist
        BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyStructureTasteGate_single_carrier_alignment_decode_encode,
      CauchyStructureTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchyStructureUp.TasteGate
