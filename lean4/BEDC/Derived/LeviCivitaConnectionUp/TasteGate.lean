import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LeviCivitaConnectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LeviCivitaConnectionUp : Type where
  | mk :
      (metric connection torsionFree metricCompatibility curvature transport replay provenance
        nameCert : BHist) ->
        LeviCivitaConnectionUp
  deriving DecidableEq

def leviCivitaConnectionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: leviCivitaConnectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: leviCivitaConnectionEncodeBHist h

def leviCivitaConnectionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (leviCivitaConnectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (leviCivitaConnectionDecodeBHist tail)

theorem LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def leviCivitaConnectionFields : LeviCivitaConnectionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LeviCivitaConnectionUp.mk metric connection torsionFree metricCompatibility curvature
      transport replay provenance nameCert =>
      [metric, connection, torsionFree, metricCompatibility, curvature, transport, replay,
        provenance, nameCert]

def leviCivitaConnectionToEventFlow : LeviCivitaConnectionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (leviCivitaConnectionFields x).map leviCivitaConnectionEncodeBHist

def leviCivitaConnectionFromEventFlow : EventFlow -> Option LeviCivitaConnectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | metric :: connection :: torsionFree :: metricCompatibility :: curvature :: transport ::
      replay :: provenance :: nameCert :: [] =>
      some
        (LeviCivitaConnectionUp.mk
          (leviCivitaConnectionDecodeBHist metric)
          (leviCivitaConnectionDecodeBHist connection)
          (leviCivitaConnectionDecodeBHist torsionFree)
          (leviCivitaConnectionDecodeBHist metricCompatibility)
          (leviCivitaConnectionDecodeBHist curvature)
          (leviCivitaConnectionDecodeBHist transport)
          (leviCivitaConnectionDecodeBHist replay)
          (leviCivitaConnectionDecodeBHist provenance)
          (leviCivitaConnectionDecodeBHist nameCert))
  | _ => none

private theorem leviCivitaConnection_round_trip :
    forall x : LeviCivitaConnectionUp,
      leviCivitaConnectionFromEventFlow (leviCivitaConnectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric connection torsionFree metricCompatibility curvature transport replay provenance
      nameCert =>
      change
        some
          (LeviCivitaConnectionUp.mk
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist metric))
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist connection))
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist torsionFree))
            (leviCivitaConnectionDecodeBHist
              (leviCivitaConnectionEncodeBHist metricCompatibility))
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist curvature))
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist transport))
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist replay))
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist provenance))
            (leviCivitaConnectionDecodeBHist (leviCivitaConnectionEncodeBHist nameCert))) =
          some
            (LeviCivitaConnectionUp.mk metric connection torsionFree metricCompatibility
              curvature transport replay provenance nameCert)
      rw [LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode metric,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode connection,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode torsionFree,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode
          metricCompatibility,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode curvature,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode transport,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode replay,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode provenance,
        LeviCivitaConnectionTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem leviCivitaConnection_toEventFlow_injective
    {x y : LeviCivitaConnectionUp} :
    leviCivitaConnectionToEventFlow x = leviCivitaConnectionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      leviCivitaConnectionFromEventFlow (leviCivitaConnectionToEventFlow x) =
        leviCivitaConnectionFromEventFlow (leviCivitaConnectionToEventFlow y) :=
    congrArg leviCivitaConnectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (leviCivitaConnection_round_trip x).symm
      (Eq.trans hread (leviCivitaConnection_round_trip y)))

private theorem leviCivitaConnection_field_faithful :
    forall x y : LeviCivitaConnectionUp, leviCivitaConnectionFields x = leviCivitaConnectionFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric₁ connection₁ torsionFree₁ metricCompatibility₁ curvature₁ transport₁ replay₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk metric₂ connection₂ torsionFree₂ metricCompatibility₂ curvature₂ transport₂ replay₂
          provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance leviCivitaConnectionBHistCarrier : BHistCarrier LeviCivitaConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := leviCivitaConnectionToEventFlow
  fromEventFlow := leviCivitaConnectionFromEventFlow

instance leviCivitaConnectionChapterTasteGate : ChapterTasteGate LeviCivitaConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => leviCivitaConnection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (leviCivitaConnection_toEventFlow_injective heq)

instance leviCivitaConnectionFieldFaithful : FieldFaithful LeviCivitaConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := leviCivitaConnectionFields
  field_faithful := leviCivitaConnection_field_faithful

instance leviCivitaConnectionNontrivial : BEDC.Meta.TasteGate.Nontrivial LeviCivitaConnectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LeviCivitaConnectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LeviCivitaConnectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def leviCivitaConnectionTasteGate : ChapterTasteGate LeviCivitaConnectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  leviCivitaConnectionChapterTasteGate

end BEDC.Derived.LeviCivitaConnectionUp
