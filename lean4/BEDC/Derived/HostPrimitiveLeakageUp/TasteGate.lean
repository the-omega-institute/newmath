import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HostPrimitiveLeakageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HostPrimitiveLeakageUp : Type where
  | mk :
      (site request replacement diagnostic failedGate auditBoundary transport replay provenance
        name : BHist) → HostPrimitiveLeakageUp
  deriving DecidableEq

def hostPrimitiveLeakageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hostPrimitiveLeakageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hostPrimitiveLeakageEncodeBHist h

def hostPrimitiveLeakageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hostPrimitiveLeakageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hostPrimitiveLeakageDecodeBHist tail)

private theorem hostPrimitiveLeakageDecode_encode_bhist :
    ∀ h : BHist,
      hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem hostPrimitiveLeakage_mk_congr
    {site site' request request' replacement replacement' diagnostic diagnostic'
      failedGate failedGate' auditBoundary auditBoundary' transport transport' replay replay'
      provenance provenance' name name' : BHist}
    (hSite : site' = site) (hRequest : request' = request)
    (hReplacement : replacement' = replacement) (hDiagnostic : diagnostic' = diagnostic)
    (hFailedGate : failedGate' = failedGate) (hAuditBoundary : auditBoundary' = auditBoundary)
    (hTransport : transport' = transport) (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance) (hName : name' = name) :
    HostPrimitiveLeakageUp.mk site' request' replacement' diagnostic' failedGate'
        auditBoundary' transport' replay' provenance' name' =
      HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
        transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSite
  cases hRequest
  cases hReplacement
  cases hDiagnostic
  cases hFailedGate
  cases hAuditBoundary
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def hostPrimitiveLeakageFields :
    HostPrimitiveLeakageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
      transport replay provenance name =>
      [site, request, replacement, diagnostic, failedGate, auditBoundary, transport, replay,
        provenance, name]

def hostPrimitiveLeakageToEventFlow :
    HostPrimitiveLeakageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hostPrimitiveLeakageFields x).map hostPrimitiveLeakageEncodeBHist

def hostPrimitiveLeakageFromEventFlow :
    EventFlow → Option HostPrimitiveLeakageUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _site :: [] => none
  | _site :: _request :: [] => none
  | _site :: _request :: _replacement :: [] => none
  | _site :: _request :: _replacement :: _diagnostic :: [] => none
  | _site :: _request :: _replacement :: _diagnostic :: _failedGate :: [] => none
  | _site :: _request :: _replacement :: _diagnostic :: _failedGate ::
      _auditBoundary :: [] => none
  | _site :: _request :: _replacement :: _diagnostic :: _failedGate ::
      _auditBoundary :: _transport :: [] => none
  | _site :: _request :: _replacement :: _diagnostic :: _failedGate ::
      _auditBoundary :: _transport :: _replay :: [] => none
  | _site :: _request :: _replacement :: _diagnostic :: _failedGate ::
      _auditBoundary :: _transport :: _replay :: _provenance :: [] => none
  | site :: request :: replacement :: diagnostic :: failedGate :: auditBoundary :: transport ::
      replay :: provenance :: name :: [] =>
      some
        (HostPrimitiveLeakageUp.mk
          (hostPrimitiveLeakageDecodeBHist site)
          (hostPrimitiveLeakageDecodeBHist request)
          (hostPrimitiveLeakageDecodeBHist replacement)
          (hostPrimitiveLeakageDecodeBHist diagnostic)
          (hostPrimitiveLeakageDecodeBHist failedGate)
          (hostPrimitiveLeakageDecodeBHist auditBoundary)
          (hostPrimitiveLeakageDecodeBHist transport)
          (hostPrimitiveLeakageDecodeBHist replay)
          (hostPrimitiveLeakageDecodeBHist provenance)
          (hostPrimitiveLeakageDecodeBHist name))
  | _site :: _request :: _replacement :: _diagnostic :: _failedGate :: _auditBoundary ::
      _transport :: _replay :: _provenance :: _name :: _extra :: _rest => none

private theorem hostPrimitiveLeakage_round_trip :
    ∀ x : HostPrimitiveLeakageUp,
      hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk site request replacement diagnostic failedGate auditBoundary transport replay provenance
      name =>
      exact
        congrArg some
          (hostPrimitiveLeakage_mk_congr
            (hostPrimitiveLeakageDecode_encode_bhist site)
            (hostPrimitiveLeakageDecode_encode_bhist request)
            (hostPrimitiveLeakageDecode_encode_bhist replacement)
            (hostPrimitiveLeakageDecode_encode_bhist diagnostic)
            (hostPrimitiveLeakageDecode_encode_bhist failedGate)
            (hostPrimitiveLeakageDecode_encode_bhist auditBoundary)
            (hostPrimitiveLeakageDecode_encode_bhist transport)
            (hostPrimitiveLeakageDecode_encode_bhist replay)
            (hostPrimitiveLeakageDecode_encode_bhist provenance)
            (hostPrimitiveLeakageDecode_encode_bhist name))

private theorem hostPrimitiveLeakageToEventFlow_injective
    {x y : HostPrimitiveLeakageUp} :
    hostPrimitiveLeakageToEventFlow x = hostPrimitiveLeakageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) =
        hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow y) :=
    congrArg hostPrimitiveLeakageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hostPrimitiveLeakage_round_trip x).symm
      (Eq.trans hread (hostPrimitiveLeakage_round_trip y)))

private theorem hostPrimitiveLeakage_field_faithful :
    ∀ x y : HostPrimitiveLeakageUp,
      hostPrimitiveLeakageFields x = hostPrimitiveLeakageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk site request replacement diagnostic failedGate auditBoundary transport replay provenance
      name =>
      cases y with
      | mk site' request' replacement' diagnostic' failedGate' auditBoundary' transport'
          replay' provenance' name' =>
          cases hfields
          rfl

instance hostPrimitiveLeakageBHistCarrier :
    BHistCarrier HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hostPrimitiveLeakageToEventFlow
  fromEventFlow := hostPrimitiveLeakageFromEventFlow

instance hostPrimitiveLeakageChapterTasteGate :
    ChapterTasteGate HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x
    exact hostPrimitiveLeakage_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hostPrimitiveLeakageToEventFlow_injective heq)

instance hostPrimitiveLeakageFieldFaithful :
    FieldFaithful HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hostPrimitiveLeakageFields
  field_faithful := hostPrimitiveLeakage_field_faithful

instance hostPrimitiveLeakageNontrivial :
    Nontrivial HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HostPrimitiveLeakageUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HostPrimitiveLeakageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HostPrimitiveLeakageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hostPrimitiveLeakageChapterTasteGate

theorem HostPrimitiveLeakageTasteGate_single_carrier_alignment :
    ChapterTasteGate HostPrimitiveLeakageUp ∧
      Nonempty (Nontrivial HostPrimitiveLeakageUp) ∧
        Nonempty (FieldFaithful HostPrimitiveLeakageUp) ∧
          (∀ h : BHist,
            hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist h) = h) ∧
          (∀ x : HostPrimitiveLeakageUp,
            hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x) ∧
          (∀ x y : HostPrimitiveLeakageUp,
            hostPrimitiveLeakageToEventFlow x = hostPrimitiveLeakageToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨hostPrimitiveLeakageChapterTasteGate, ⟨hostPrimitiveLeakageNontrivial⟩,
      ⟨hostPrimitiveLeakageFieldFaithful⟩, hostPrimitiveLeakageDecode_encode_bhist,
      hostPrimitiveLeakage_round_trip,
      fun _ _ heq => hostPrimitiveLeakageToEventFlow_injective heq⟩

end BEDC.Derived.HostPrimitiveLeakageUp
