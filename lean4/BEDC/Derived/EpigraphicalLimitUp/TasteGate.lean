import BEDC.Derived.EpigraphicalLimitUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EpigraphicalLimitUp.TasteGate

open BEDC.Derived.EpigraphicalLimitUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def epigraphicalLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: epigraphicalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: epigraphicalLimitEncodeBHist h

def epigraphicalLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (epigraphicalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (epigraphicalLimitDecodeBHist tail)

private theorem EpigraphicalLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, epigraphicalLimitDecodeBHist (epigraphicalLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def epigraphicalLimitToEventFlow : EpigraphicalLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EpigraphicalLimitUp.finiteEpigraphWindowCertificate => [[]]

def epigraphicalLimitFromEventFlow : EventFlow → Option EpigraphicalLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | event :: rest =>
      match rest with
      | [] =>
          match event with
          | [] => some EpigraphicalLimitUp.finiteEpigraphWindowCertificate
          | _ :: _ => none
      | _ :: _ => none

private theorem EpigraphicalLimitTasteGate_single_carrier_alignment_round_trip
    (x : EpigraphicalLimitUp) :
    epigraphicalLimitFromEventFlow (epigraphicalLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x
  rfl

private theorem EpigraphicalLimitToEventFlow_injective {x y : EpigraphicalLimitUp} :
    epigraphicalLimitToEventFlow x = epigraphicalLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

instance epigraphicalLimitBHistCarrier : BHistCarrier EpigraphicalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := epigraphicalLimitToEventFlow
  fromEventFlow := epigraphicalLimitFromEventFlow

instance epigraphicalLimitChapterTasteGate : ChapterTasteGate EpigraphicalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change epigraphicalLimitFromEventFlow (epigraphicalLimitToEventFlow x) = some x
    exact EpigraphicalLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EpigraphicalLimitToEventFlow_injective heq)

theorem EpigraphicalLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, epigraphicalLimitDecodeBHist (epigraphicalLimitEncodeBHist h) = h) ∧
      (∀ x : EpigraphicalLimitUp,
        epigraphicalLimitFromEventFlow (epigraphicalLimitToEventFlow x) = some x) ∧
        (∀ x y : EpigraphicalLimitUp,
          epigraphicalLimitToEventFlow x = epigraphicalLimitToEventFlow y → x = y) ∧
          epigraphicalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EpigraphicalLimitTasteGate_single_carrier_alignment_decode_encode,
      EpigraphicalLimitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => EpigraphicalLimitToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EpigraphicalLimitUp.TasteGate
