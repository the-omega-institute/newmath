import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingTraceClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingTraceClassifierUp : Type where
  | mk (machine history finiteTrace positive refusal transport route provenance localName :
      BHist) : HaltingTraceClassifierUp
  deriving DecidableEq

def haltingTraceClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingTraceClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingTraceClassifierEncodeBHist h

def haltingTraceClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingTraceClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingTraceClassifierDecodeBHist tail)

private theorem haltingTraceClassifierDecode_encode_bhist :
    ∀ h : BHist,
      haltingTraceClassifierDecodeBHist
        (haltingTraceClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def haltingTraceClassifierToEventFlow : HaltingTraceClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingTraceClassifierUp.mk machine history finiteTrace positive refusal transport route provenance localName =>
      [[BMark.b0],
        haltingTraceClassifierEncodeBHist machine,
        [BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist history,
        [BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist finiteTrace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist positive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        haltingTraceClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        haltingTraceClassifierEncodeBHist localName]

def haltingTraceClassifierFromEventFlow :
    EventFlow → Option HaltingTraceClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | machine :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | history :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | finiteTrace :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | positive :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (HaltingTraceClassifierUp.mk
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    machine)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    history)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    finiteTrace)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    positive)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    refusal)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    transport)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    route)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    provenance)
                                                                                  (haltingTraceClassifierDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem haltingTraceClassifier_round_trip :
    ∀ x : HaltingTraceClassifierUp,
      haltingTraceClassifierFromEventFlow
        (haltingTraceClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk machine history finiteTrace positive refusal transport route provenance localName =>
      change
        some
          (HaltingTraceClassifierUp.mk
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist machine))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist history))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist finiteTrace))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist positive))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist refusal))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist transport))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist route))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist provenance))
            (haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist localName))) =
          some
            (HaltingTraceClassifierUp.mk machine history finiteTrace positive refusal
              transport route provenance localName)
      rw [haltingTraceClassifierDecode_encode_bhist machine,
        haltingTraceClassifierDecode_encode_bhist history,
        haltingTraceClassifierDecode_encode_bhist finiteTrace,
        haltingTraceClassifierDecode_encode_bhist positive,
        haltingTraceClassifierDecode_encode_bhist refusal,
        haltingTraceClassifierDecode_encode_bhist transport,
        haltingTraceClassifierDecode_encode_bhist route,
        haltingTraceClassifierDecode_encode_bhist provenance,
        haltingTraceClassifierDecode_encode_bhist localName]

private theorem haltingTraceClassifierToEventFlow_injective
    {x y : HaltingTraceClassifierUp} :
    haltingTraceClassifierToEventFlow x =
      haltingTraceClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingTraceClassifierFromEventFlow (haltingTraceClassifierToEventFlow x) =
        haltingTraceClassifierFromEventFlow (haltingTraceClassifierToEventFlow y) :=
    congrArg haltingTraceClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (haltingTraceClassifier_round_trip x).symm
      (Eq.trans hread (haltingTraceClassifier_round_trip y)))

instance haltingTraceClassifierBHistCarrier :
    BHistCarrier HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingTraceClassifierToEventFlow
  fromEventFlow := haltingTraceClassifierFromEventFlow

instance haltingTraceClassifierChapterTasteGate :
    ChapterTasteGate HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      haltingTraceClassifierFromEventFlow
        (haltingTraceClassifierToEventFlow x) = some x
    exact haltingTraceClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (haltingTraceClassifierToEventFlow_injective heq)

instance haltingTraceClassifierFieldFaithful :
    FieldFaithful HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | HaltingTraceClassifierUp.mk machine history finiteTrace positive refusal transport
        route provenance localName =>
        [machine, history, finiteTrace, positive, refusal, transport, route, provenance,
          localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk machine₁ history₁ finiteTrace₁ positive₁ refusal₁ transport₁ route₁
        provenance₁ localName₁ =>
        cases y with
        | mk machine₂ history₂ finiteTrace₂ positive₂ refusal₂ transport₂ route₂
            provenance₂ localName₂ =>
            cases hfields
            rfl

instance haltingTraceClassifierNontrivial :
    Nontrivial HaltingTraceClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HaltingTraceClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HaltingTraceClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HaltingTraceClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  haltingTraceClassifierChapterTasteGate

theorem HaltingTraceClassifierTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HaltingTraceClassifierUp) ∧
      Nonempty (FieldFaithful HaltingTraceClassifierUp) ∧
        Nonempty (Nontrivial HaltingTraceClassifierUp) ∧
          (∀ h : BHist,
            haltingTraceClassifierDecodeBHist
              (haltingTraceClassifierEncodeBHist h) = h) ∧
            (∀ x : HaltingTraceClassifierUp,
              haltingTraceClassifierFromEventFlow
                (haltingTraceClassifierToEventFlow x) = some x) ∧
              (∀ x y : HaltingTraceClassifierUp,
                haltingTraceClassifierToEventFlow x =
                  haltingTraceClassifierToEventFlow y → x = y) ∧
                haltingTraceClassifierEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨haltingTraceClassifierChapterTasteGate⟩
  · constructor
    · exact ⟨haltingTraceClassifierFieldFaithful⟩
    · constructor
      · exact ⟨haltingTraceClassifierNontrivial⟩
      · constructor
        · exact haltingTraceClassifierDecode_encode_bhist
        · constructor
          · exact haltingTraceClassifier_round_trip
          · constructor
            · intro x y heq
              exact haltingTraceClassifierToEventFlow_injective heq
            · rfl

end BEDC.Derived.HaltingTraceClassifierUp
