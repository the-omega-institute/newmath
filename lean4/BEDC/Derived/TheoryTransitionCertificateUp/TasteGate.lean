import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TheoryTransitionCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TheoryTransitionCertificateUp : Type where
  | mk :
      (oldState successor signature classifier stability ledger failure transport route
        provenance name : BHist) →
      TheoryTransitionCertificateUp
  deriving DecidableEq

def theoryTransitionCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: theoryTransitionCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: theoryTransitionCertificateEncodeBHist h

def theoryTransitionCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (theoryTransitionCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (theoryTransitionCertificateDecodeBHist tail)

private theorem theoryTransitionCertificateDecode_encode_bhist :
    ∀ h : BHist,
      theoryTransitionCertificateDecodeBHist
        (theoryTransitionCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def theoryTransitionCertificateToEventFlow :
    TheoryTransitionCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TheoryTransitionCertificateUp.mk oldState successor signature classifier stability ledger
      failure transport route provenance name =>
      [[BMark.b0],
        theoryTransitionCertificateEncodeBHist oldState,
        [BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist successor,
        [BMark.b1, BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist signature,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        theoryTransitionCertificateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoryTransitionCertificateEncodeBHist name]

def theoryTransitionCertificateFromEventFlow :
    EventFlow → Option TheoryTransitionCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | oldState :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | successor :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | signature :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | stability :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | failure :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | route :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (TheoryTransitionCertificateUp.mk
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    oldState)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    successor)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    signature)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    classifier)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    stability)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    ledger)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    failure)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    transport)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    route)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    provenance)
                                                                                                  (theoryTransitionCertificateDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ => none

private theorem theoryTransitionCertificate_round_trip :
    ∀ x : TheoryTransitionCertificateUp,
      theoryTransitionCertificateFromEventFlow
        (theoryTransitionCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk oldState successor signature classifier stability ledger failure transport route
      provenance name =>
      change
        some
          (TheoryTransitionCertificateUp.mk
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist oldState))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist successor))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist signature))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist classifier))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist stability))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist ledger))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist failure))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist transport))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist route))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist provenance))
            (theoryTransitionCertificateDecodeBHist
              (theoryTransitionCertificateEncodeBHist name))) =
          some
            (TheoryTransitionCertificateUp.mk oldState successor signature classifier
              stability ledger failure transport route provenance name)
      rw [theoryTransitionCertificateDecode_encode_bhist oldState,
        theoryTransitionCertificateDecode_encode_bhist successor,
        theoryTransitionCertificateDecode_encode_bhist signature,
        theoryTransitionCertificateDecode_encode_bhist classifier,
        theoryTransitionCertificateDecode_encode_bhist stability,
        theoryTransitionCertificateDecode_encode_bhist ledger,
        theoryTransitionCertificateDecode_encode_bhist failure,
        theoryTransitionCertificateDecode_encode_bhist transport,
        theoryTransitionCertificateDecode_encode_bhist route,
        theoryTransitionCertificateDecode_encode_bhist provenance,
        theoryTransitionCertificateDecode_encode_bhist name]

private theorem theoryTransitionCertificateToEventFlow_injective
    {x y : TheoryTransitionCertificateUp} :
    theoryTransitionCertificateToEventFlow x =
      theoryTransitionCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      theoryTransitionCertificateFromEventFlow
          (theoryTransitionCertificateToEventFlow x) =
        theoryTransitionCertificateFromEventFlow
          (theoryTransitionCertificateToEventFlow y) :=
    congrArg theoryTransitionCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (theoryTransitionCertificate_round_trip x).symm
      (Eq.trans hread (theoryTransitionCertificate_round_trip y)))

instance theoryTransitionCertificateBHistCarrier :
    BHistCarrier TheoryTransitionCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := theoryTransitionCertificateToEventFlow
  fromEventFlow := theoryTransitionCertificateFromEventFlow

instance theoryTransitionCertificateChapterTasteGate :
    ChapterTasteGate TheoryTransitionCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      theoryTransitionCertificateFromEventFlow
        (theoryTransitionCertificateToEventFlow x) = some x
    exact theoryTransitionCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (theoryTransitionCertificateToEventFlow_injective heq)

instance theoryTransitionCertificateFieldFaithful :
    FieldFaithful TheoryTransitionCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TheoryTransitionCertificateUp.mk oldState successor signature classifier stability ledger
        failure transport route provenance name =>
        [oldState, successor, signature, classifier, stability, ledger, failure, transport,
          route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk oldState₁ successor₁ signature₁ classifier₁ stability₁ ledger₁ failure₁ transport₁
        route₁ provenance₁ name₁ =>
        cases y with
        | mk oldState₂ successor₂ signature₂ classifier₂ stability₂ ledger₂ failure₂
            transport₂ route₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance theoryTransitionCertificateNontrivial :
    Nontrivial TheoryTransitionCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TheoryTransitionCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TheoryTransitionCertificateUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TheoryTransitionCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  theoryTransitionCertificateChapterTasteGate

theorem TheoryTransitionCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      theoryTransitionCertificateDecodeBHist
        (theoryTransitionCertificateEncodeBHist h) = h) ∧
      (∀ x : TheoryTransitionCertificateUp,
        theoryTransitionCertificateFromEventFlow
          (theoryTransitionCertificateToEventFlow x) = some x) ∧
        (∀ x y : TheoryTransitionCertificateUp,
          theoryTransitionCertificateToEventFlow x =
            theoryTransitionCertificateToEventFlow y → x = y) ∧
          theoryTransitionCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact theoryTransitionCertificateDecode_encode_bhist
  · constructor
    · exact theoryTransitionCertificate_round_trip
    · constructor
      · intro x y heq
        exact theoryTransitionCertificateToEventFlow_injective heq
      · rfl

def theoryTransitionCertificateFields :
    TheoryTransitionCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TheoryTransitionCertificateUp.mk oldState successor signature classifier stability ledger
      failure transport route provenance name =>
      [oldState, successor, signature, classifier, stability, ledger, failure, transport,
        route, provenance, name]

theorem TheoryTransitionCertificateUp_single_carrier_alignment :
    (∀ h : BHist,
      theoryTransitionCertificateDecodeBHist
        (theoryTransitionCertificateEncodeBHist h) = h) ∧
      (∀ x : TheoryTransitionCertificateUp,
        theoryTransitionCertificateFromEventFlow
          (theoryTransitionCertificateToEventFlow x) = some x) ∧
      (∀ x y : TheoryTransitionCertificateUp,
        theoryTransitionCertificateToEventFlow x =
          theoryTransitionCertificateToEventFlow y → x = y) ∧
      Nonempty (ChapterTasteGate TheoryTransitionCertificateUp) ∧
      (∀ x y : TheoryTransitionCertificateUp,
        theoryTransitionCertificateFields x =
          theoryTransitionCertificateFields y → x = y) ∧
      (∀ x : TheoryTransitionCertificateUp,
        ∃ h : BHist, List.Mem h (theoryTransitionCertificateFields x)) ∧
      theoryTransitionCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact theoryTransitionCertificateDecode_encode_bhist
  · constructor
    · exact theoryTransitionCertificate_round_trip
    · constructor
      · intro x y heq
        exact theoryTransitionCertificateToEventFlow_injective heq
      · constructor
        · exact ⟨theoryTransitionCertificateChapterTasteGate⟩
        · constructor
          · intro x y h
            cases x with
            | mk oldState₁ successor₁ signature₁ classifier₁ stability₁ ledger₁ failure₁
                transport₁ route₁ provenance₁ name₁ =>
                cases y with
                | mk oldState₂ successor₂ signature₂ classifier₂ stability₂ ledger₂
                    failure₂ transport₂ route₂ provenance₂ name₂ =>
                    simp only [theoryTransitionCertificateFields] at h
                    cases h
                    rfl
          · constructor
            · intro x
              cases x with
              | mk oldState successor signature classifier stability ledger failure transport
                  route provenance name =>
                  exact ⟨oldState, List.Mem.head _⟩
            · rfl

end BEDC.Derived.TheoryTransitionCertificateUp
