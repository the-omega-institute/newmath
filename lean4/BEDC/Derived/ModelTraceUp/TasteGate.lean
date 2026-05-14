import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModelTraceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModelTraceUp : Type where
  | mk :
      (orbit output corpus refusal inscription observer readback transport route provenance
        nameCert : BHist) →
      ModelTraceUp

def modelTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modelTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modelTraceEncodeBHist h

def modelTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modelTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modelTraceDecodeBHist tail)

private theorem modelTraceDecode_encode_bhist :
    ∀ h : BHist, modelTraceDecodeBHist (modelTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modelTraceToEventFlow : ModelTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModelTraceUp.mk orbit output corpus refusal inscription observer readback transport route
      provenance nameCert =>
      [[BMark.b0],
        modelTraceEncodeBHist orbit,
        [BMark.b1, BMark.b0],
        modelTraceEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist corpus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist inscription,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist observer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modelTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        modelTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist nameCert]

private def modelTraceDecodeEventRows : Nat → EventFlow → Option (List RawEvent)
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => some []
  | Nat.zero, _ :: _ => none
  | Nat.succ _, [] => none
  | Nat.succ n, _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match modelTraceDecodeEventRows n rest1 with
          | none => none
          | some rows => some (row :: rows)

def modelTraceFromEventFlow : EventFlow → Option ModelTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      match modelTraceDecodeEventRows 11 ef with
      | none => none
      | some rows =>
          match rows with
          | [] => none
          | orbit :: rest0 =>
              match rest0 with
              | [] => none
              | output :: rest1 =>
                  match rest1 with
                  | [] => none
                  | corpus :: rest2 =>
                      match rest2 with
                      | [] => none
                      | refusal :: rest3 =>
                          match rest3 with
                          | [] => none
                          | inscription :: rest4 =>
                              match rest4 with
                              | [] => none
                              | observer :: rest5 =>
                                  match rest5 with
                                  | [] => none
                                  | readback :: rest6 =>
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
                                                  | nameCert :: rest10 =>
                                                      match rest10 with
                                                      | [] =>
                                                          some
                                                            (ModelTraceUp.mk
                                                              (modelTraceDecodeBHist orbit)
                                                              (modelTraceDecodeBHist output)
                                                              (modelTraceDecodeBHist corpus)
                                                              (modelTraceDecodeBHist refusal)
                                                              (modelTraceDecodeBHist inscription)
                                                              (modelTraceDecodeBHist observer)
                                                              (modelTraceDecodeBHist readback)
                                                              (modelTraceDecodeBHist transport)
                                                              (modelTraceDecodeBHist route)
                                                              (modelTraceDecodeBHist provenance)
                                                              (modelTraceDecodeBHist nameCert))
                                                      | _ :: _ => none

private theorem modelTrace_round_trip :
    ∀ x : ModelTraceUp, modelTraceFromEventFlow (modelTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk orbit output corpus refusal inscription observer readback transport route provenance
      nameCert =>
      change
        some
          (ModelTraceUp.mk
            (modelTraceDecodeBHist (modelTraceEncodeBHist orbit))
            (modelTraceDecodeBHist (modelTraceEncodeBHist output))
            (modelTraceDecodeBHist (modelTraceEncodeBHist corpus))
            (modelTraceDecodeBHist (modelTraceEncodeBHist refusal))
            (modelTraceDecodeBHist (modelTraceEncodeBHist inscription))
            (modelTraceDecodeBHist (modelTraceEncodeBHist observer))
            (modelTraceDecodeBHist (modelTraceEncodeBHist readback))
            (modelTraceDecodeBHist (modelTraceEncodeBHist transport))
            (modelTraceDecodeBHist (modelTraceEncodeBHist route))
            (modelTraceDecodeBHist (modelTraceEncodeBHist provenance))
            (modelTraceDecodeBHist (modelTraceEncodeBHist nameCert))) =
          some
            (ModelTraceUp.mk orbit output corpus refusal inscription observer readback
              transport route provenance nameCert)
      rw [modelTraceDecode_encode_bhist orbit, modelTraceDecode_encode_bhist output,
        modelTraceDecode_encode_bhist corpus, modelTraceDecode_encode_bhist refusal,
        modelTraceDecode_encode_bhist inscription, modelTraceDecode_encode_bhist observer,
        modelTraceDecode_encode_bhist readback, modelTraceDecode_encode_bhist transport,
        modelTraceDecode_encode_bhist route, modelTraceDecode_encode_bhist provenance,
        modelTraceDecode_encode_bhist nameCert]

private theorem modelTraceToEventFlow_injective {x y : ModelTraceUp} :
    modelTraceToEventFlow x = modelTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modelTraceFromEventFlow (modelTraceToEventFlow x) =
        modelTraceFromEventFlow (modelTraceToEventFlow y) :=
    congrArg modelTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modelTrace_round_trip x).symm
      (Eq.trans hread (modelTrace_round_trip y)))

instance modelTraceBHistCarrier : BHistCarrier ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modelTraceToEventFlow
  fromEventFlow := modelTraceFromEventFlow

instance modelTraceChapterTasteGate : ChapterTasteGate ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modelTraceFromEventFlow (modelTraceToEventFlow x) = some x
    exact modelTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modelTraceToEventFlow_injective heq)

instance modelTraceFieldFaithful : FieldFaithful ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ModelTraceUp.mk orbit output corpus refusal inscription observer readback transport route
        provenance nameCert =>
        [orbit, output, corpus, refusal, inscription, observer, readback, transport, route,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk orbit₁ output₁ corpus₁ refusal₁ inscription₁ observer₁ readback₁ transport₁
        route₁ provenance₁ nameCert₁ =>
      cases y with
      | mk orbit₂ output₂ corpus₂ refusal₂ inscription₂ observer₂ readback₂ transport₂
          route₂ provenance₂ nameCert₂ =>
        injection h with hOrbit t1
        injection t1 with hOutput t2
        injection t2 with hCorpus t3
        injection t3 with hRefusal t4
        injection t4 with hInscription t5
        injection t5 with hObserver t6
        injection t6 with hReadback t7
        injection t7 with hTransport t8
        injection t8 with hRoute t9
        injection t9 with hProvenance t10
        injection t10 with hNameCert _
        cases hOrbit
        cases hOutput
        cases hCorpus
        cases hRefusal
        cases hInscription
        cases hObserver
        cases hReadback
        cases hTransport
        cases hRoute
        cases hProvenance
        cases hNameCert
        rfl

instance modelTraceNontrivial : Nontrivial ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModelTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ModelTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ModelTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modelTraceChapterTasteGate

theorem ModelTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, modelTraceDecodeBHist (modelTraceEncodeBHist h) = h) ∧
      (∀ x : ModelTraceUp, modelTraceFromEventFlow (modelTraceToEventFlow x) = some x) ∧
        (∀ x y : ModelTraceUp, modelTraceToEventFlow x = modelTraceToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful ModelTraceUp) ∧ Nonempty (Nontrivial ModelTraceUp) ∧
            modelTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact modelTraceDecode_encode_bhist
  · constructor
    · exact modelTrace_round_trip
    · constructor
      · intro x y heq
        exact modelTraceToEventFlow_injective heq
      · constructor
        · exact ⟨modelTraceFieldFaithful⟩
        · constructor
          · exact ⟨modelTraceNontrivial⟩
          · rfl

end BEDC.Derived.ModelTraceUp.TasteGate

namespace BEDC.Derived.ModelTraceUp

def taste_gate :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.ModelTraceUp
