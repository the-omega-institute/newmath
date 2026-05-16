import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnticAdequacyAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnticAdequacyAuditUp : Type where
  | mk :
      (source audit schedule readback real classifier ledger transport route provenance
        name : BHist) →
      OnticAdequacyAuditUp
  deriving DecidableEq

def onticAdequacyAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onticAdequacyAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onticAdequacyAuditEncodeBHist h

def onticAdequacyAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onticAdequacyAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onticAdequacyAuditDecodeBHist tail)

private theorem onticAdequacyAuditDecode_encode_bhist :
    ∀ h : BHist, onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem onticAdequacyAudit_mk_congr
    {source source' audit audit' schedule schedule' readback readback' real real'
      classifier classifier' ledger ledger' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hSource : source' = source)
    (hAudit : audit' = audit)
    (hSchedule : schedule' = schedule)
    (hReadback : readback' = readback)
    (hReal : real' = real)
    (hClassifier : classifier' = classifier)
    (hLedger : ledger' = ledger)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    OnticAdequacyAuditUp.mk source' audit' schedule' readback' real' classifier'
        ledger' transport' route' provenance' name' =
      OnticAdequacyAuditUp.mk source audit schedule readback real classifier ledger
        transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hAudit
  cases hSchedule
  cases hReadback
  cases hReal
  cases hClassifier
  cases hLedger
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def onticAdequacyAuditFields : OnticAdequacyAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnticAdequacyAuditUp.mk source audit schedule readback real classifier ledger transport
      route provenance name =>
      [source, audit, schedule, readback, real, classifier, ledger, transport, route,
        provenance, name]

def onticAdequacyAuditToEventFlow : OnticAdequacyAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (onticAdequacyAuditFields x).map onticAdequacyAuditEncodeBHist

def onticAdequacyAuditFromEventFlow : EventFlow → Option OnticAdequacyAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | audit :: rest1 =>
          match rest1 with
          | [] => none
          | schedule :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | real :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | route :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | name :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (OnticAdequacyAuditUp.mk
                                                      (onticAdequacyAuditDecodeBHist source)
                                                      (onticAdequacyAuditDecodeBHist audit)
                                                      (onticAdequacyAuditDecodeBHist schedule)
                                                      (onticAdequacyAuditDecodeBHist readback)
                                                      (onticAdequacyAuditDecodeBHist real)
                                                      (onticAdequacyAuditDecodeBHist classifier)
                                                      (onticAdequacyAuditDecodeBHist ledger)
                                                      (onticAdequacyAuditDecodeBHist transport)
                                                      (onticAdequacyAuditDecodeBHist route)
                                                      (onticAdequacyAuditDecodeBHist provenance)
                                                      (onticAdequacyAuditDecodeBHist name))
                                              | _ :: _ => none

private theorem onticAdequacyAudit_round_trip :
    ∀ x : OnticAdequacyAuditUp,
      onticAdequacyAuditFromEventFlow (onticAdequacyAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source audit schedule readback real classifier ledger transport route provenance name =>
      change
        some
          (OnticAdequacyAuditUp.mk
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist source))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist audit))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist schedule))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist readback))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist real))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist classifier))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist ledger))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist transport))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist route))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist provenance))
            (onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist name))) =
          some
            (OnticAdequacyAuditUp.mk source audit schedule readback real classifier ledger
              transport route provenance name)
      exact
        congrArg some
          (onticAdequacyAudit_mk_congr
            (onticAdequacyAuditDecode_encode_bhist source)
            (onticAdequacyAuditDecode_encode_bhist audit)
            (onticAdequacyAuditDecode_encode_bhist schedule)
            (onticAdequacyAuditDecode_encode_bhist readback)
            (onticAdequacyAuditDecode_encode_bhist real)
            (onticAdequacyAuditDecode_encode_bhist classifier)
            (onticAdequacyAuditDecode_encode_bhist ledger)
            (onticAdequacyAuditDecode_encode_bhist transport)
            (onticAdequacyAuditDecode_encode_bhist route)
            (onticAdequacyAuditDecode_encode_bhist provenance)
            (onticAdequacyAuditDecode_encode_bhist name))

private theorem onticAdequacyAuditToEventFlow_injective {x y : OnticAdequacyAuditUp} :
    onticAdequacyAuditToEventFlow x = onticAdequacyAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onticAdequacyAuditFromEventFlow (onticAdequacyAuditToEventFlow x) =
        onticAdequacyAuditFromEventFlow (onticAdequacyAuditToEventFlow y) :=
    congrArg onticAdequacyAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (onticAdequacyAudit_round_trip x).symm
      (Eq.trans hread (onticAdequacyAudit_round_trip y)))

private theorem onticAdequacyAudit_fields_faithful :
    ∀ x y : OnticAdequacyAuditUp,
      onticAdequacyAuditFields x = onticAdequacyAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ audit₁ schedule₁ readback₁ real₁ classifier₁ ledger₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk source₂ audit₂ schedule₂ readback₂ real₂ classifier₂ ledger₂ transport₂ route₂
          provenance₂ name₂ =>
          simp only [onticAdequacyAuditFields] at h
          cases h
          rfl

def onticAdequacyAuditCarrier : BHistCarrier OnticAdequacyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticAdequacyAuditToEventFlow
  fromEventFlow := onticAdequacyAuditFromEventFlow

instance onticAdequacyAuditBHistCarrier : BHistCarrier OnticAdequacyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticAdequacyAuditToEventFlow
  fromEventFlow := onticAdequacyAuditFromEventFlow

instance onticAdequacyAuditChapterTasteGate : ChapterTasteGate OnticAdequacyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change onticAdequacyAuditFromEventFlow (onticAdequacyAuditToEventFlow x) = some x
    exact onticAdequacyAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (onticAdequacyAuditToEventFlow_injective heq)

instance onticAdequacyAuditFieldFaithful : FieldFaithful OnticAdequacyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := onticAdequacyAuditFields
  field_faithful := onticAdequacyAudit_fields_faithful

instance onticAdequacyAuditNontrivial : Nontrivial OnticAdequacyAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OnticAdequacyAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OnticAdequacyAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hSource
        cases hSource⟩

theorem OnticAdequacyAuditTasteGate_single_carrier_alignment :
    (∀ x : OnticAdequacyAuditUp,
      onticAdequacyAuditFromEventFlow (onticAdequacyAuditToEventFlow x) = some x) ∧
      (∀ x y : OnticAdequacyAuditUp,
        onticAdequacyAuditToEventFlow x = onticAdequacyAuditToEventFlow y → x = y) ∧
        (∀ x y : OnticAdequacyAuditUp,
          onticAdequacyAuditFields x = onticAdequacyAuditFields y → x = y) ∧
          Nonempty (Nontrivial OnticAdequacyAuditUp) ∧
          (∀ h : BHist,
            onticAdequacyAuditDecodeBHist (onticAdequacyAuditEncodeBHist h) = h) ∧
            onticAdequacyAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨onticAdequacyAudit_round_trip, by
      intro x y heq
      exact onticAdequacyAuditToEventFlow_injective heq,
      onticAdequacyAudit_fields_faithful, ⟨onticAdequacyAuditNontrivial⟩,
      onticAdequacyAuditDecode_encode_bhist, rfl⟩

end BEDC.Derived.OnticAdequacyAuditUp
