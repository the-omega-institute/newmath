import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InterHistSynchronizationRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InterHistSynchronizationRefusalUp : Type where
  | mk :
      (leftStream rightStream token refusalLedger transport replay provenance name : BHist) →
      InterHistSynchronizationRefusalUp
  deriving DecidableEq

def interHistSynchronizationRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: interHistSynchronizationRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: interHistSynchronizationRefusalEncodeBHist h

def interHistSynchronizationRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (interHistSynchronizationRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (interHistSynchronizationRefusalDecodeBHist tail)

private theorem interHistSynchronizationRefusalDecode_encode_bhist :
    ∀ h : BHist,
      interHistSynchronizationRefusalDecodeBHist
        (interHistSynchronizationRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem interHistSynchronizationRefusal_mk_congr
    {leftStream leftStream' rightStream rightStream' token token' refusalLedger
      refusalLedger' transport transport' replay replay' provenance provenance' name name' :
        BHist}
    (hLeft : leftStream' = leftStream)
    (hRight : rightStream' = rightStream)
    (hToken : token' = token)
    (hRefusal : refusalLedger' = refusalLedger)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    InterHistSynchronizationRefusalUp.mk leftStream' rightStream' token' refusalLedger'
        transport' replay' provenance' name' =
      InterHistSynchronizationRefusalUp.mk leftStream rightStream token refusalLedger
        transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hLeft
  cases hRight
  cases hToken
  cases hRefusal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def interHistSynchronizationRefusalToEventFlow :
    InterHistSynchronizationRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InterHistSynchronizationRefusalUp.mk leftStream rightStream token refusalLedger
      transport replay provenance name =>
      [[BMark.b0],
        interHistSynchronizationRefusalEncodeBHist leftStream,
        [BMark.b1, BMark.b0],
        interHistSynchronizationRefusalEncodeBHist rightStream,
        [BMark.b1, BMark.b1, BMark.b0],
        interHistSynchronizationRefusalEncodeBHist token,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSynchronizationRefusalEncodeBHist refusalLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSynchronizationRefusalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSynchronizationRefusalEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSynchronizationRefusalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        interHistSynchronizationRefusalEncodeBHist name]

def interHistSynchronizationRefusalFromEventFlow :
    EventFlow → Option InterHistSynchronizationRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | leftStream :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rightStream :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | token :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusalLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (InterHistSynchronizationRefusalUp.mk
                                                                          (interHistSynchronizationRefusalDecodeBHist leftStream)
                                                                          (interHistSynchronizationRefusalDecodeBHist rightStream)
                                                                          (interHistSynchronizationRefusalDecodeBHist token)
                                                                          (interHistSynchronizationRefusalDecodeBHist refusalLedger)
                                                                          (interHistSynchronizationRefusalDecodeBHist transport)
                                                                          (interHistSynchronizationRefusalDecodeBHist replay)
                                                                          (interHistSynchronizationRefusalDecodeBHist provenance)
                                                                          (interHistSynchronizationRefusalDecodeBHist name))
                                                                  | _ :: _ => none

private theorem interHistSynchronizationRefusal_round_trip :
    ∀ x : InterHistSynchronizationRefusalUp,
      interHistSynchronizationRefusalFromEventFlow
        (interHistSynchronizationRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftStream rightStream token refusalLedger transport replay provenance name =>
      change
        some
          (InterHistSynchronizationRefusalUp.mk
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist leftStream))
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist rightStream))
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist token))
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist refusalLedger))
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist transport))
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist replay))
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist provenance))
            (interHistSynchronizationRefusalDecodeBHist
              (interHistSynchronizationRefusalEncodeBHist name))) =
          some
            (InterHistSynchronizationRefusalUp.mk leftStream rightStream token
              refusalLedger transport replay provenance name)
      exact
        congrArg some
          (interHistSynchronizationRefusal_mk_congr
            (interHistSynchronizationRefusalDecode_encode_bhist leftStream)
            (interHistSynchronizationRefusalDecode_encode_bhist rightStream)
            (interHistSynchronizationRefusalDecode_encode_bhist token)
            (interHistSynchronizationRefusalDecode_encode_bhist refusalLedger)
            (interHistSynchronizationRefusalDecode_encode_bhist transport)
            (interHistSynchronizationRefusalDecode_encode_bhist replay)
            (interHistSynchronizationRefusalDecode_encode_bhist provenance)
            (interHistSynchronizationRefusalDecode_encode_bhist name))

private theorem interHistSynchronizationRefusalToEventFlow_injective
    {x y : InterHistSynchronizationRefusalUp} :
    interHistSynchronizationRefusalToEventFlow x =
      interHistSynchronizationRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      interHistSynchronizationRefusalFromEventFlow
          (interHistSynchronizationRefusalToEventFlow x) =
        interHistSynchronizationRefusalFromEventFlow
          (interHistSynchronizationRefusalToEventFlow y) :=
    congrArg interHistSynchronizationRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (interHistSynchronizationRefusal_round_trip x).symm
      (Eq.trans hread (interHistSynchronizationRefusal_round_trip y)))

instance interHistSynchronizationRefusalBHistCarrier :
    BHistCarrier InterHistSynchronizationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := interHistSynchronizationRefusalToEventFlow
  fromEventFlow := interHistSynchronizationRefusalFromEventFlow

instance interHistSynchronizationRefusalChapterTasteGate :
    ChapterTasteGate InterHistSynchronizationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      interHistSynchronizationRefusalFromEventFlow
        (interHistSynchronizationRefusalToEventFlow x) = some x
    exact interHistSynchronizationRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (interHistSynchronizationRefusalToEventFlow_injective heq)

def interHistSynchronizationRefusalFields :
    InterHistSynchronizationRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InterHistSynchronizationRefusalUp.mk leftStream rightStream token refusalLedger
      transport replay provenance name =>
      [leftStream, rightStream, token, refusalLedger, transport, replay, provenance, name]

private theorem interHistSynchronizationRefusal_field_faithful_concrete :
    ∀ x y : InterHistSynchronizationRefusalUp,
      interHistSynchronizationRefusalFields x =
        interHistSynchronizationRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk leftStream rightStream token refusalLedger transport replay provenance name =>
      cases y with
      | mk leftStream' rightStream' token' refusalLedger' transport' replay'
          provenance' name' =>
          injection hfields with hLeft tail0
          injection tail0 with hRight tail1
          injection tail1 with hToken tail2
          injection tail2 with hRefusal tail3
          injection tail3 with hTransport tail4
          injection tail4 with hReplay tail5
          injection tail5 with hProvenance tail6
          injection tail6 with hName _hNil
          cases hLeft
          cases hRight
          cases hToken
          cases hRefusal
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hName
          rfl

instance interHistSynchronizationRefusalFieldFaithful :
    FieldFaithful InterHistSynchronizationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := interHistSynchronizationRefusalFields
  field_faithful := interHistSynchronizationRefusal_field_faithful_concrete

private def interHistSynchronizationRefusal_nontrivial_witness :
    Σ' (x : InterHistSynchronizationRefusalUp) (y : InterHistSynchronizationRefusalUp), x ≠ y :=
  ⟨InterHistSynchronizationRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    InterHistSynchronizationRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      -- BEDC touchpoint anchor: BHist BMark
      intro h
      cases h⟩

instance interHistSynchronizationRefusalNontrivial :
    Nontrivial InterHistSynchronizationRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := interHistSynchronizationRefusal_nontrivial_witness

theorem InterHistSynchronizationRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      interHistSynchronizationRefusalDecodeBHist
        (interHistSynchronizationRefusalEncodeBHist h) = h) ∧
      (∀ x : InterHistSynchronizationRefusalUp,
        interHistSynchronizationRefusalFromEventFlow
          (interHistSynchronizationRefusalToEventFlow x) = some x) ∧
        (∀ x y : InterHistSynchronizationRefusalUp,
          interHistSynchronizationRefusalToEventFlow x =
            interHistSynchronizationRefusalToEventFlow y → x = y) ∧
          interHistSynchronizationRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact interHistSynchronizationRefusalDecode_encode_bhist
  · constructor
    · exact interHistSynchronizationRefusal_round_trip
    · constructor
      · intro x y heq
        exact interHistSynchronizationRefusalToEventFlow_injective heq
      · rfl

end BEDC.Derived.InterHistSynchronizationRefusalUp
