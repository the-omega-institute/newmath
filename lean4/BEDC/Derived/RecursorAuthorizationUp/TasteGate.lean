import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorAuthorizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RecursorAuthorizationUp : Type where
  | mk :
      (inductiveName signature recursor motive branches descent transports continuations
        provenance name : BHist) →
      RecursorAuthorizationUp
  deriving DecidableEq

def recursorAuthorizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorAuthorizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorAuthorizationEncodeBHist h

def recursorAuthorizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorAuthorizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorAuthorizationDecodeBHist tail)

private theorem recursorAuthorizationDecodeEncodeBHist :
    ∀ h : BHist,
      recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def recursorAuthorizationFields : RecursorAuthorizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorAuthorizationUp.mk inductiveName signature recursor motive branches descent
      transports continuations provenance name =>
      [inductiveName, signature, recursor, motive, branches, descent, transports,
        continuations, provenance, name]

def recursorAuthorizationToEventFlow : RecursorAuthorizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (recursorAuthorizationFields x).map recursorAuthorizationEncodeBHist

def recursorAuthorizationFromEventFlow :
    EventFlow → Option RecursorAuthorizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | inductiveName :: rest0 =>
      match rest0 with
      | [] => none
      | signature :: rest1 =>
          match rest1 with
          | [] => none
          | recursor :: rest2 =>
              match rest2 with
              | [] => none
              | motive :: rest3 =>
                  match rest3 with
                  | [] => none
                  | branches :: rest4 =>
                      match rest4 with
                      | [] => none
                      | descent :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transports :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuations :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (RecursorAuthorizationUp.mk
                                                  (recursorAuthorizationDecodeBHist
                                                    inductiveName)
                                                  (recursorAuthorizationDecodeBHist
                                                    signature)
                                                  (recursorAuthorizationDecodeBHist
                                                    recursor)
                                                  (recursorAuthorizationDecodeBHist
                                                    motive)
                                                  (recursorAuthorizationDecodeBHist
                                                    branches)
                                                  (recursorAuthorizationDecodeBHist
                                                    descent)
                                                  (recursorAuthorizationDecodeBHist
                                                    transports)
                                                  (recursorAuthorizationDecodeBHist
                                                    continuations)
                                                  (recursorAuthorizationDecodeBHist
                                                    provenance)
                                                  (recursorAuthorizationDecodeBHist name))
                                          | _ :: _ => none

private theorem recursorAuthorization_round_trip :
    ∀ x : RecursorAuthorizationUp,
      recursorAuthorizationFromEventFlow (recursorAuthorizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inductiveName signature recursor motive branches descent transports continuations
      provenance name =>
      change
        some
          (RecursorAuthorizationUp.mk
            (recursorAuthorizationDecodeBHist
              (recursorAuthorizationEncodeBHist inductiveName))
            (recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist signature))
            (recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist recursor))
            (recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist motive))
            (recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist branches))
            (recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist descent))
            (recursorAuthorizationDecodeBHist
              (recursorAuthorizationEncodeBHist transports))
            (recursorAuthorizationDecodeBHist
              (recursorAuthorizationEncodeBHist continuations))
            (recursorAuthorizationDecodeBHist
              (recursorAuthorizationEncodeBHist provenance))
            (recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist name))) =
          some
            (RecursorAuthorizationUp.mk inductiveName signature recursor motive branches
              descent transports continuations provenance name)
      rw [recursorAuthorizationDecodeEncodeBHist inductiveName,
        recursorAuthorizationDecodeEncodeBHist signature,
        recursorAuthorizationDecodeEncodeBHist recursor,
        recursorAuthorizationDecodeEncodeBHist motive,
        recursorAuthorizationDecodeEncodeBHist branches,
        recursorAuthorizationDecodeEncodeBHist descent,
        recursorAuthorizationDecodeEncodeBHist transports,
        recursorAuthorizationDecodeEncodeBHist continuations,
        recursorAuthorizationDecodeEncodeBHist provenance,
        recursorAuthorizationDecodeEncodeBHist name]

private theorem recursorAuthorizationToEventFlow_injective
    {x y : RecursorAuthorizationUp} :
    recursorAuthorizationToEventFlow x =
      recursorAuthorizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorAuthorizationFromEventFlow (recursorAuthorizationToEventFlow x) =
        recursorAuthorizationFromEventFlow (recursorAuthorizationToEventFlow y) :=
    congrArg recursorAuthorizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorAuthorization_round_trip x).symm
      (Eq.trans hread (recursorAuthorization_round_trip y)))

private theorem recursorAuthorization_field_faithful :
    ∀ x y : RecursorAuthorizationUp,
      recursorAuthorizationFields x = recursorAuthorizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk inductiveName signature recursor motive branches descent transports continuations
      provenance name =>
      cases y with
      | mk inductiveName' signature' recursor' motive' branches' descent' transports'
          continuations' provenance' name' =>
          cases hfields
          rfl

instance recursorAuthorizationBHistCarrier :
    BHistCarrier RecursorAuthorizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := recursorAuthorizationToEventFlow
  fromEventFlow := recursorAuthorizationFromEventFlow

instance recursorAuthorizationChapterTasteGate :
    ChapterTasteGate RecursorAuthorizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      recursorAuthorizationFromEventFlow (recursorAuthorizationToEventFlow x) = some x
    exact recursorAuthorization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (recursorAuthorizationToEventFlow_injective heq)

instance recursorAuthorizationFieldFaithful :
    FieldFaithful RecursorAuthorizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := recursorAuthorizationFields
  field_faithful := recursorAuthorization_field_faithful

instance recursorAuthorizationNontrivial :
    Nontrivial RecursorAuthorizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RecursorAuthorizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RecursorAuthorizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RecursorAuthorizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  recursorAuthorizationChapterTasteGate

theorem RecursorAuthorizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      recursorAuthorizationDecodeBHist (recursorAuthorizationEncodeBHist h) = h) ∧
      (∀ x : RecursorAuthorizationUp,
        recursorAuthorizationFromEventFlow (recursorAuthorizationToEventFlow x) =
          some x) ∧
        (∀ x y : RecursorAuthorizationUp,
          recursorAuthorizationToEventFlow x =
            recursorAuthorizationToEventFlow y → x = y) ∧
          recursorAuthorizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact recursorAuthorizationDecodeEncodeBHist
  · constructor
    · exact recursorAuthorization_round_trip
    · constructor
      · intro x y heq
        exact recursorAuthorizationToEventFlow_injective heq
      · rfl

end BEDC.Derived.RecursorAuthorizationUp
