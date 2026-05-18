import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoAbsoluteBridgeAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NoAbsoluteBridgeAuditUp : Type where
  | mk :
      (bridge targetHost encoding decoding unsupported leakage registry recognizer transport replay
        provenance name : BHist) →
        NoAbsoluteBridgeAuditUp
  deriving DecidableEq

def noAbsoluteBridgeAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noAbsoluteBridgeAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noAbsoluteBridgeAuditEncodeBHist h

def noAbsoluteBridgeAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noAbsoluteBridgeAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noAbsoluteBridgeAuditDecodeBHist tail)

private theorem noAbsoluteBridgeAuditDecode_encode_bhist :
    ∀ h : BHist,
      noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def noAbsoluteBridgeAuditToEventFlow : NoAbsoluteBridgeAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NoAbsoluteBridgeAuditUp.mk bridge targetHost encoding decoding unsupported leakage registry
      recognizer transport replay provenance name =>
      [noAbsoluteBridgeAuditEncodeBHist bridge,
        noAbsoluteBridgeAuditEncodeBHist targetHost,
        noAbsoluteBridgeAuditEncodeBHist encoding,
        noAbsoluteBridgeAuditEncodeBHist decoding,
        noAbsoluteBridgeAuditEncodeBHist unsupported,
        noAbsoluteBridgeAuditEncodeBHist leakage,
        noAbsoluteBridgeAuditEncodeBHist registry,
        noAbsoluteBridgeAuditEncodeBHist recognizer,
        noAbsoluteBridgeAuditEncodeBHist transport,
        noAbsoluteBridgeAuditEncodeBHist replay,
        noAbsoluteBridgeAuditEncodeBHist provenance,
        noAbsoluteBridgeAuditEncodeBHist name]

def noAbsoluteBridgeAuditFromEventFlow :
    EventFlow → Option NoAbsoluteBridgeAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | bridge :: rest0 =>
      match rest0 with
      | [] => none
      | targetHost :: rest1 =>
          match rest1 with
          | [] => none
          | encoding :: rest2 =>
              match rest2 with
              | [] => none
              | decoding :: rest3 =>
                  match rest3 with
                  | [] => none
                  | unsupported :: rest4 =>
                      match rest4 with
                      | [] => none
                      | leakage :: rest5 =>
                          match rest5 with
                          | [] => none
                          | registry :: rest6 =>
                              match rest6 with
                              | [] => none
                              | recognizer :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (NoAbsoluteBridgeAuditUp.mk
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            bridge)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            targetHost)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            encoding)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            decoding)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            unsupported)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            leakage)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            registry)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            recognizer)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            transport)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            replay)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            provenance)
                                                          (noAbsoluteBridgeAuditDecodeBHist
                                                            name))
                                                  | _ :: _ => none

private theorem noAbsoluteBridgeAudit_round_trip :
    ∀ x : NoAbsoluteBridgeAuditUp,
      noAbsoluteBridgeAuditFromEventFlow (noAbsoluteBridgeAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bridge targetHost encoding decoding unsupported leakage registry recognizer transport replay
      provenance name =>
      change
        some
          (NoAbsoluteBridgeAuditUp.mk
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist bridge))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist targetHost))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist encoding))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist decoding))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist unsupported))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist leakage))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist registry))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist recognizer))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist transport))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist replay))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist provenance))
            (noAbsoluteBridgeAuditDecodeBHist (noAbsoluteBridgeAuditEncodeBHist name))) =
          some
            (NoAbsoluteBridgeAuditUp.mk bridge targetHost encoding decoding unsupported leakage
              registry recognizer transport replay provenance name)
      rw [noAbsoluteBridgeAuditDecode_encode_bhist bridge,
        noAbsoluteBridgeAuditDecode_encode_bhist targetHost,
        noAbsoluteBridgeAuditDecode_encode_bhist encoding,
        noAbsoluteBridgeAuditDecode_encode_bhist decoding,
        noAbsoluteBridgeAuditDecode_encode_bhist unsupported,
        noAbsoluteBridgeAuditDecode_encode_bhist leakage,
        noAbsoluteBridgeAuditDecode_encode_bhist registry,
        noAbsoluteBridgeAuditDecode_encode_bhist recognizer,
        noAbsoluteBridgeAuditDecode_encode_bhist transport,
        noAbsoluteBridgeAuditDecode_encode_bhist replay,
        noAbsoluteBridgeAuditDecode_encode_bhist provenance,
        noAbsoluteBridgeAuditDecode_encode_bhist name]

private theorem noAbsoluteBridgeAuditToEventFlow_injective
    {x y : NoAbsoluteBridgeAuditUp} :
    noAbsoluteBridgeAuditToEventFlow x = noAbsoluteBridgeAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noAbsoluteBridgeAuditFromEventFlow (noAbsoluteBridgeAuditToEventFlow x) =
        noAbsoluteBridgeAuditFromEventFlow (noAbsoluteBridgeAuditToEventFlow y) :=
    congrArg noAbsoluteBridgeAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (noAbsoluteBridgeAudit_round_trip x).symm
      (Eq.trans hread (noAbsoluteBridgeAudit_round_trip y)))

instance noAbsoluteBridgeAuditBHistCarrier : BHistCarrier NoAbsoluteBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noAbsoluteBridgeAuditToEventFlow
  fromEventFlow := noAbsoluteBridgeAuditFromEventFlow

instance noAbsoluteBridgeAuditChapterTasteGateInst :
    ChapterTasteGate NoAbsoluteBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change noAbsoluteBridgeAuditFromEventFlow (noAbsoluteBridgeAuditToEventFlow x) = some x
    exact noAbsoluteBridgeAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (noAbsoluteBridgeAuditToEventFlow_injective heq)

def noAbsoluteBridgeAuditChapterTasteGate : ChapterTasteGate NoAbsoluteBridgeAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  noAbsoluteBridgeAuditChapterTasteGateInst

instance noAbsoluteBridgeAuditFieldFaithful : FieldFaithful NoAbsoluteBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | NoAbsoluteBridgeAuditUp.mk bridge targetHost encoding decoding unsupported leakage registry
        recognizer transport replay provenance name =>
        [bridge, targetHost, encoding, decoding, unsupported, leakage, registry, recognizer,
          transport, replay, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk bridge₁ targetHost₁ encoding₁ decoding₁ unsupported₁ leakage₁ registry₁ recognizer₁
        transport₁ replay₁ provenance₁ name₁ =>
        cases y with
        | mk bridge₂ targetHost₂ encoding₂ decoding₂ unsupported₂ leakage₂ registry₂ recognizer₂
            transport₂ replay₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance noAbsoluteBridgeAuditNontrivial : Nontrivial NoAbsoluteBridgeAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NoAbsoluteBridgeAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NoAbsoluteBridgeAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hb _ _ _ _ _ _ _ _ _ _ _
        cases hb⟩

end BEDC.Derived.NoAbsoluteBridgeAuditUp
