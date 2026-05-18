import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypingJudgmentClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypingJudgmentClassifierUp : Type where
  | mk :
      (judgment membership derivation sigReadback contReplay transport provenance localName :
        BHist) →
      TypingJudgmentClassifierUp
  deriving DecidableEq

def typingJudgmentClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typingJudgmentClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typingJudgmentClassifierEncodeBHist h

def typingJudgmentClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typingJudgmentClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typingJudgmentClassifierDecodeBHist tail)

private theorem typingJudgmentClassifierDecode_encode_bhist :
    ∀ h : BHist,
      typingJudgmentClassifierDecodeBHist (typingJudgmentClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def typingJudgmentClassifierToEventFlow : TypingJudgmentClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TypingJudgmentClassifierUp.mk judgment membership derivation sigReadback contReplay
      transport provenance localName =>
      [[BMark.b0],
        typingJudgmentClassifierEncodeBHist judgment,
        [BMark.b1, BMark.b0],
        typingJudgmentClassifierEncodeBHist membership,
        [BMark.b1, BMark.b1, BMark.b0],
        typingJudgmentClassifierEncodeBHist derivation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typingJudgmentClassifierEncodeBHist sigReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typingJudgmentClassifierEncodeBHist contReplay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typingJudgmentClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typingJudgmentClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        typingJudgmentClassifierEncodeBHist localName]

def typingJudgmentClassifierFromEventFlow : EventFlow → Option TypingJudgmentClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | judgment :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | membership :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | derivation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sigReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | contReplay :: rest9 =>
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
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | localName :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (TypingJudgmentClassifierUp.mk
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            judgment)
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            membership)
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            derivation)
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            sigReadback)
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            contReplay)
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            transport)
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            provenance)
                                                                          (typingJudgmentClassifierDecodeBHist
                                                                            localName))
                                                                  | _ :: _ => none

private theorem typingJudgmentClassifier_round_trip :
    ∀ x : TypingJudgmentClassifierUp,
      typingJudgmentClassifierFromEventFlow (typingJudgmentClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk judgment membership derivation sigReadback contReplay transport provenance localName =>
      change
        some
          (TypingJudgmentClassifierUp.mk
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist judgment))
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist membership))
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist derivation))
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist sigReadback))
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist contReplay))
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist transport))
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist provenance))
            (typingJudgmentClassifierDecodeBHist
              (typingJudgmentClassifierEncodeBHist localName))) =
          some
            (TypingJudgmentClassifierUp.mk judgment membership derivation sigReadback
              contReplay transport provenance localName)
      rw [typingJudgmentClassifierDecode_encode_bhist judgment,
        typingJudgmentClassifierDecode_encode_bhist membership,
        typingJudgmentClassifierDecode_encode_bhist derivation,
        typingJudgmentClassifierDecode_encode_bhist sigReadback,
        typingJudgmentClassifierDecode_encode_bhist contReplay,
        typingJudgmentClassifierDecode_encode_bhist transport,
        typingJudgmentClassifierDecode_encode_bhist provenance,
        typingJudgmentClassifierDecode_encode_bhist localName]

private theorem typingJudgmentClassifierToEventFlow_injective
    {x y : TypingJudgmentClassifierUp} :
    typingJudgmentClassifierToEventFlow x = typingJudgmentClassifierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typingJudgmentClassifierFromEventFlow (typingJudgmentClassifierToEventFlow x) =
        typingJudgmentClassifierFromEventFlow (typingJudgmentClassifierToEventFlow y) :=
    congrArg typingJudgmentClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (typingJudgmentClassifier_round_trip x).symm
      (Eq.trans hread (typingJudgmentClassifier_round_trip y)))

instance typingJudgmentClassifierBHistCarrier :
    BHistCarrier TypingJudgmentClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typingJudgmentClassifierToEventFlow
  fromEventFlow := typingJudgmentClassifierFromEventFlow

instance typingJudgmentClassifierChapterTasteGate :
    ChapterTasteGate TypingJudgmentClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      typingJudgmentClassifierFromEventFlow (typingJudgmentClassifierToEventFlow x) =
        some x
    exact typingJudgmentClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typingJudgmentClassifierToEventFlow_injective heq)

instance typingJudgmentClassifierFieldFaithful :
    FieldFaithful TypingJudgmentClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TypingJudgmentClassifierUp.mk judgment membership derivation sigReadback contReplay
        transport provenance localName =>
        [judgment, membership, derivation, sigReadback, contReplay, transport, provenance,
          localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk judgment1 membership1 derivation1 sigReadback1 contReplay1 transport1 provenance1
        localName1 =>
        cases y with
        | mk judgment2 membership2 derivation2 sigReadback2 contReplay2 transport2
            provenance2 localName2 =>
            cases h
            rfl

instance typingJudgmentClassifierNontrivial :
    Nontrivial TypingJudgmentClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypingJudgmentClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypingJudgmentClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TypingJudgmentClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  typingJudgmentClassifierChapterTasteGate

theorem TypingJudgmentClassifierCarrier_derivation_route
    (x : TypingJudgmentClassifierUp) :
    ∃ judgment membership derivation sigReadback contReplay transport provenance
        localName : BHist,
      x = TypingJudgmentClassifierUp.mk judgment membership derivation sigReadback contReplay
        transport provenance localName ∧
        typingJudgmentClassifierFromEventFlow (typingJudgmentClassifierToEventFlow x) =
          some x ∧
          typingJudgmentClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk judgment membership derivation sigReadback contReplay transport provenance localName =>
      refine
        ⟨judgment, membership, derivation, sigReadback, contReplay, transport, provenance,
          localName, ?_⟩
      constructor
      · rfl
      · constructor
        · exact typingJudgmentClassifier_round_trip
            (TypingJudgmentClassifierUp.mk judgment membership derivation sigReadback
              contReplay transport provenance localName)
        · rfl

namespace TasteGate

theorem TypingJudgmentClassifierTasteGate_readiness :
    (∀ h : BHist,
      typingJudgmentClassifierDecodeBHist (typingJudgmentClassifierEncodeBHist h) = h) ∧
      (∀ x : TypingJudgmentClassifierUp,
        typingJudgmentClassifierFromEventFlow (typingJudgmentClassifierToEventFlow x) =
          some x) ∧
        (∀ x y : TypingJudgmentClassifierUp,
          typingJudgmentClassifierToEventFlow x = typingJudgmentClassifierToEventFlow y →
            x = y) ∧
          typingJudgmentClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact typingJudgmentClassifierDecode_encode_bhist
  · constructor
    · intro x
      exact typingJudgmentClassifier_round_trip x
    · constructor
      · intro x y heq
        exact typingJudgmentClassifierToEventFlow_injective heq
      · rfl

end TasteGate

theorem TypingJudgmentClassifierUp_taste_gate_readiness :
    ChapterTasteGate TypingJudgmentClassifierUp ∧
      Nonempty (Nontrivial TypingJudgmentClassifierUp) ∧
        Nonempty (FieldFaithful TypingJudgmentClassifierUp) ∧
        (∀ h : BHist,
          typingJudgmentClassifierDecodeBHist (typingJudgmentClassifierEncodeBHist h) = h) ∧
          typingJudgmentClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨typingJudgmentClassifierChapterTasteGate, ⟨typingJudgmentClassifierNontrivial⟩,
      ⟨typingJudgmentClassifierFieldFaithful⟩, typingJudgmentClassifierDecode_encode_bhist,
      rfl⟩

end BEDC.Derived.TypingJudgmentClassifierUp
