import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingDistinctionTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingDistinctionTraceUp : Type where
  | mk :
      (admitted trace distinction diagonal transport route provenance cert : BHist) →
      HaltingDistinctionTraceUp
  deriving DecidableEq

def haltingDistinctionTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingDistinctionTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingDistinctionTraceEncodeBHist h

def haltingDistinctionTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingDistinctionTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingDistinctionTraceDecodeBHist tail)

private theorem HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      haltingDistinctionTraceDecodeBHist (haltingDistinctionTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem HaltingDistinctionTraceTasteGate_single_carrier_alignment_mk_congr
    {admitted admitted' trace trace' distinction distinction' diagonal diagonal'
      transport transport' route route' provenance provenance' cert cert' : BHist}
    (hAdmitted : admitted' = admitted)
    (hTrace : trace' = trace)
    (hDistinction : distinction' = distinction)
    (hDiagonal : diagonal' = diagonal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hCert : cert' = cert) :
    HaltingDistinctionTraceUp.mk admitted' trace' distinction' diagonal' transport' route'
        provenance' cert' =
      HaltingDistinctionTraceUp.mk admitted trace distinction diagonal transport route provenance
        cert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hAdmitted
  cases hTrace
  cases hDistinction
  cases hDiagonal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hCert
  rfl

def haltingDistinctionTraceFields : HaltingDistinctionTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingDistinctionTraceUp.mk admitted trace distinction diagonal transport route provenance
      cert =>
      [admitted, trace, distinction, diagonal, transport, route, provenance, cert]

def haltingDistinctionTraceToEventFlow : HaltingDistinctionTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingDistinctionTraceUp.mk admitted trace distinction diagonal transport route provenance
      cert =>
      [haltingDistinctionTraceEncodeBHist admitted,
        haltingDistinctionTraceEncodeBHist trace,
        haltingDistinctionTraceEncodeBHist distinction,
        haltingDistinctionTraceEncodeBHist diagonal,
        haltingDistinctionTraceEncodeBHist transport,
        haltingDistinctionTraceEncodeBHist route,
        haltingDistinctionTraceEncodeBHist provenance,
        haltingDistinctionTraceEncodeBHist cert]

private def HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default index rest

def haltingDistinctionTraceFromEventFlow (ef : EventFlow) : Option HaltingDistinctionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HaltingDistinctionTraceUp.mk
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 0 ef))
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 1 ef))
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 2 ef))
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 3 ef))
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 4 ef))
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 5 ef))
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 6 ef))
      (haltingDistinctionTraceDecodeBHist
        (HaltingDistinctionTraceTasteGate_single_carrier_alignment_event_at_default 7 ef)))

private theorem HaltingDistinctionTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HaltingDistinctionTraceUp,
      haltingDistinctionTraceFromEventFlow (haltingDistinctionTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk admitted trace distinction diagonal transport route provenance cert =>
      exact
        congrArg some
          (HaltingDistinctionTraceTasteGate_single_carrier_alignment_mk_congr
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode admitted)
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode trace)
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode distinction)
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode diagonal)
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode transport)
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode route)
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode provenance)
            (HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode cert))

private theorem HaltingDistinctionTraceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HaltingDistinctionTraceUp} :
    haltingDistinctionTraceToEventFlow x = haltingDistinctionTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingDistinctionTraceFromEventFlow (haltingDistinctionTraceToEventFlow x) =
        haltingDistinctionTraceFromEventFlow (haltingDistinctionTraceToEventFlow y) :=
    congrArg haltingDistinctionTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HaltingDistinctionTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HaltingDistinctionTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem HaltingDistinctionTraceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : HaltingDistinctionTraceUp,
      haltingDistinctionTraceFields x = haltingDistinctionTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk admitted trace distinction diagonal transport route provenance cert =>
      cases y with
      | mk admitted' trace' distinction' diagonal' transport' route' provenance' cert' =>
          cases hfields
          rfl

instance haltingDistinctionTraceBHistCarrier : BHistCarrier HaltingDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingDistinctionTraceToEventFlow
  fromEventFlow := haltingDistinctionTraceFromEventFlow

instance haltingDistinctionTraceChapterTasteGate :
    ChapterTasteGate HaltingDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change haltingDistinctionTraceFromEventFlow (haltingDistinctionTraceToEventFlow x) = some x
    exact HaltingDistinctionTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HaltingDistinctionTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance haltingDistinctionTraceFieldFaithful :
    FieldFaithful HaltingDistinctionTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := haltingDistinctionTraceFields
  field_faithful := HaltingDistinctionTraceTasteGate_single_carrier_alignment_field_faithful

def taste_gate : ChapterTasteGate HaltingDistinctionTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  haltingDistinctionTraceChapterTasteGate

theorem HaltingDistinctionTraceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier HaltingDistinctionTraceUp) ∧
      Nonempty (ChapterTasteGate HaltingDistinctionTraceUp) ∧
        Nonempty (FieldFaithful HaltingDistinctionTraceUp) ∧
          (∀ h : BHist,
            haltingDistinctionTraceDecodeBHist (haltingDistinctionTraceEncodeBHist h) = h) ∧
            (∀ x : HaltingDistinctionTraceUp,
              haltingDistinctionTraceFromEventFlow (haltingDistinctionTraceToEventFlow x) =
                some x) ∧
              (∀ x y : HaltingDistinctionTraceUp,
                haltingDistinctionTraceToEventFlow x = haltingDistinctionTraceToEventFlow y →
                  x = y) ∧
                haltingDistinctionTraceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨haltingDistinctionTraceBHistCarrier⟩,
      ⟨haltingDistinctionTraceChapterTasteGate⟩,
      ⟨haltingDistinctionTraceFieldFaithful⟩,
      HaltingDistinctionTraceTasteGate_single_carrier_alignment_decode,
      HaltingDistinctionTraceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HaltingDistinctionTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HaltingDistinctionTraceUp
