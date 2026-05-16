import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReflectiveInquiryUp : Type where
  | mk
      (physical formal signature classifier package transport ledger replay continuation
        openContinuation localName : BHist) :
      ReflectiveInquiryUp

def reflectiveInquiryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reflectiveInquiryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reflectiveInquiryEncodeBHist h

def reflectiveInquiryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reflectiveInquiryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reflectiveInquiryDecodeBHist tail)

private theorem reflectiveInquiryDecode_encode_bhist :
    ∀ h : BHist, reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def reflectiveInquiryToEventFlow : ReflectiveInquiryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectiveInquiryUp.mk physical formal signature classifier package transport ledger replay
      continuation openContinuation localName =>
      [reflectiveInquiryEncodeBHist physical,
        reflectiveInquiryEncodeBHist formal,
        reflectiveInquiryEncodeBHist signature,
        reflectiveInquiryEncodeBHist classifier,
        reflectiveInquiryEncodeBHist package,
        reflectiveInquiryEncodeBHist transport,
        reflectiveInquiryEncodeBHist ledger,
        reflectiveInquiryEncodeBHist replay,
        reflectiveInquiryEncodeBHist continuation,
        reflectiveInquiryEncodeBHist openContinuation,
        reflectiveInquiryEncodeBHist localName]

def reflectiveInquiryFromEventFlow : EventFlow → Option ReflectiveInquiryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | physical :: rest0 =>
      match rest0 with
      | [] => none
      | formal :: rest1 =>
          match rest1 with
          | [] => none
          | signature :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | package :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | continuation :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | openContinuation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ReflectiveInquiryUp.mk
                                                      (reflectiveInquiryDecodeBHist physical)
                                                      (reflectiveInquiryDecodeBHist formal)
                                                      (reflectiveInquiryDecodeBHist signature)
                                                      (reflectiveInquiryDecodeBHist classifier)
                                                      (reflectiveInquiryDecodeBHist package)
                                                      (reflectiveInquiryDecodeBHist transport)
                                                      (reflectiveInquiryDecodeBHist ledger)
                                                      (reflectiveInquiryDecodeBHist replay)
                                                      (reflectiveInquiryDecodeBHist continuation)
                                                      (reflectiveInquiryDecodeBHist openContinuation)
                                                      (reflectiveInquiryDecodeBHist localName))
                                              | _ :: _ => none

private theorem reflectiveInquiry_round_trip :
    ∀ x : ReflectiveInquiryUp,
      reflectiveInquiryFromEventFlow (reflectiveInquiryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk physical formal signature classifier package transport ledger replay continuation
      openContinuation localName =>
      change
        some
          (ReflectiveInquiryUp.mk
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist physical))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist formal))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist signature))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist classifier))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist package))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist transport))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist ledger))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist replay))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist continuation))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist openContinuation))
            (reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist localName))) =
          some
            (ReflectiveInquiryUp.mk physical formal signature classifier package transport ledger
              replay continuation openContinuation localName)
      rw [reflectiveInquiryDecode_encode_bhist physical,
        reflectiveInquiryDecode_encode_bhist formal,
        reflectiveInquiryDecode_encode_bhist signature,
        reflectiveInquiryDecode_encode_bhist classifier,
        reflectiveInquiryDecode_encode_bhist package,
        reflectiveInquiryDecode_encode_bhist transport,
        reflectiveInquiryDecode_encode_bhist ledger,
        reflectiveInquiryDecode_encode_bhist replay,
        reflectiveInquiryDecode_encode_bhist continuation,
        reflectiveInquiryDecode_encode_bhist openContinuation,
        reflectiveInquiryDecode_encode_bhist localName]

private theorem reflectiveInquiryToEventFlow_injective {x y : ReflectiveInquiryUp} :
    reflectiveInquiryToEventFlow x = reflectiveInquiryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reflectiveInquiryFromEventFlow (reflectiveInquiryToEventFlow x) =
        reflectiveInquiryFromEventFlow (reflectiveInquiryToEventFlow y) :=
    congrArg reflectiveInquiryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reflectiveInquiry_round_trip x).symm
      (Eq.trans hread (reflectiveInquiry_round_trip y)))

private def reflectiveInquiryFields : ReflectiveInquiryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectiveInquiryUp.mk physical formal signature classifier package transport ledger replay
      continuation openContinuation localName =>
      [physical, formal, signature, classifier, package, transport, ledger, replay,
        continuation, openContinuation, localName]

private theorem reflectiveInquiry_field_faithful :
    ∀ x y : ReflectiveInquiryUp,
      reflectiveInquiryFields x = reflectiveInquiryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk physical₁ formal₁ signature₁ classifier₁ package₁ transport₁ ledger₁ replay₁
      continuation₁ openContinuation₁ localName₁ =>
      cases y with
      | mk physical₂ formal₂ signature₂ classifier₂ package₂ transport₂ ledger₂ replay₂
          continuation₂ openContinuation₂ localName₂ =>
          cases h
          rfl

instance reflectiveInquiryBHistCarrier : BHistCarrier ReflectiveInquiryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reflectiveInquiryToEventFlow
  fromEventFlow := reflectiveInquiryFromEventFlow

instance reflectiveInquiryChapterTasteGate : ChapterTasteGate ReflectiveInquiryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reflectiveInquiryFromEventFlow (reflectiveInquiryToEventFlow x) = some x
    exact reflectiveInquiry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reflectiveInquiryToEventFlow_injective heq)

instance reflectiveInquiryFieldFaithful : FieldFaithful ReflectiveInquiryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reflectiveInquiryFields
  field_faithful := reflectiveInquiry_field_faithful

instance reflectiveInquiryNontrivial : Nontrivial ReflectiveInquiryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReflectiveInquiryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ReflectiveInquiryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ReflectiveInquiryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  reflectiveInquiryChapterTasteGate

theorem ReflectiveInquiryTasteGate_single_carrier_alignment :
    (∀ h : BHist, reflectiveInquiryDecodeBHist (reflectiveInquiryEncodeBHist h) = h) ∧
      (∀ x : ReflectiveInquiryUp,
        reflectiveInquiryFromEventFlow (reflectiveInquiryToEventFlow x) = some x) ∧
      (∀ x y : ReflectiveInquiryUp,
        reflectiveInquiryToEventFlow x = reflectiveInquiryToEventFlow y → x = y) ∧
      reflectiveInquiryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨reflectiveInquiryDecode_encode_bhist, reflectiveInquiry_round_trip,
      (fun _x _y heq => reflectiveInquiryToEventFlow_injective heq), rfl⟩

theorem ReflectiveInquiryUp_source_separation_transport
    {physical formal signature classifier package transport ledger replay continuation
      openContinuation localName physical2 formal2 signature2 classifier2 package2 transport2
      ledger2 replay2 continuation2 openContinuation2 localName2 : BHist} :
    reflectiveInquiryToEventFlow
        (ReflectiveInquiryUp.mk physical formal signature classifier package transport ledger
          replay continuation openContinuation localName) =
      reflectiveInquiryToEventFlow
        (ReflectiveInquiryUp.mk physical2 formal2 signature2 classifier2 package2 transport2
          ledger2 replay2 continuation2 openContinuation2 localName2) →
        Cont physical formal continuation →
          Cont physical2 formal2 continuation2 ∧ hsame physical physical2 ∧
            hsame formal formal2 ∧ hsame continuation continuation2 := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro heq hCont
  have hPacket :
      ReflectiveInquiryUp.mk physical formal signature classifier package transport ledger
          replay continuation openContinuation localName =
        ReflectiveInquiryUp.mk physical2 formal2 signature2 classifier2 package2 transport2
          ledger2 replay2 continuation2 openContinuation2 localName2 :=
    reflectiveInquiryToEventFlow_injective heq
  cases hPacket
  exact ⟨hCont, rfl, rfl, rfl⟩

end BEDC.Derived.ReflectiveInquiryUp
