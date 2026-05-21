import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuthorizedRecursorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuthorizedRecursorUp : Type where
  | mk :
      (inductiveName signature motive branches output authorization transports continuations
        provenance name : BHist) →
      AuthorizedRecursorUp
  deriving DecidableEq

def authorizedRecursorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: authorizedRecursorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: authorizedRecursorEncodeBHist h

def authorizedRecursorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (authorizedRecursorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (authorizedRecursorDecodeBHist tail)

private theorem authorizedRecursorDecodeEncodeBHist :
    ∀ h : BHist,
      authorizedRecursorDecodeBHist (authorizedRecursorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def authorizedRecursorFields : AuthorizedRecursorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuthorizedRecursorUp.mk inductiveName signature motive branches output authorization
      transports continuations provenance name =>
      [inductiveName, signature, motive, branches, output, authorization, transports,
        continuations, provenance, name]

def authorizedRecursorToEventFlow : AuthorizedRecursorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (authorizedRecursorFields x).map authorizedRecursorEncodeBHist

def authorizedRecursorFromEventFlow :
    EventFlow → Option AuthorizedRecursorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | inductiveName :: rest0 =>
      match rest0 with
      | [] => none
      | signature :: rest1 =>
          match rest1 with
          | [] => none
          | motive :: rest2 =>
              match rest2 with
              | [] => none
              | branches :: rest3 =>
                  match rest3 with
                  | [] => none
                  | output :: rest4 =>
                      match rest4 with
                      | [] => none
                      | authorization :: rest5 =>
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
                                                (AuthorizedRecursorUp.mk
                                                  (authorizedRecursorDecodeBHist
                                                    inductiveName)
                                                  (authorizedRecursorDecodeBHist
                                                    signature)
                                                  (authorizedRecursorDecodeBHist motive)
                                                  (authorizedRecursorDecodeBHist branches)
                                                  (authorizedRecursorDecodeBHist output)
                                                  (authorizedRecursorDecodeBHist
                                                    authorization)
                                                  (authorizedRecursorDecodeBHist
                                                    transports)
                                                  (authorizedRecursorDecodeBHist
                                                    continuations)
                                                  (authorizedRecursorDecodeBHist
                                                    provenance)
                                                  (authorizedRecursorDecodeBHist name))
                                          | _ :: _ => none

private theorem authorizedRecursor_round_trip :
    ∀ x : AuthorizedRecursorUp,
      authorizedRecursorFromEventFlow (authorizedRecursorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inductiveName signature motive branches output authorization transports continuations
      provenance name =>
      change
        some
          (AuthorizedRecursorUp.mk
            (authorizedRecursorDecodeBHist
              (authorizedRecursorEncodeBHist inductiveName))
            (authorizedRecursorDecodeBHist (authorizedRecursorEncodeBHist signature))
            (authorizedRecursorDecodeBHist (authorizedRecursorEncodeBHist motive))
            (authorizedRecursorDecodeBHist (authorizedRecursorEncodeBHist branches))
            (authorizedRecursorDecodeBHist (authorizedRecursorEncodeBHist output))
            (authorizedRecursorDecodeBHist
              (authorizedRecursorEncodeBHist authorization))
            (authorizedRecursorDecodeBHist
              (authorizedRecursorEncodeBHist transports))
            (authorizedRecursorDecodeBHist
              (authorizedRecursorEncodeBHist continuations))
            (authorizedRecursorDecodeBHist
              (authorizedRecursorEncodeBHist provenance))
            (authorizedRecursorDecodeBHist (authorizedRecursorEncodeBHist name))) =
          some
            (AuthorizedRecursorUp.mk inductiveName signature motive branches output
              authorization transports continuations provenance name)
      rw [authorizedRecursorDecodeEncodeBHist inductiveName,
        authorizedRecursorDecodeEncodeBHist signature,
        authorizedRecursorDecodeEncodeBHist motive,
        authorizedRecursorDecodeEncodeBHist branches,
        authorizedRecursorDecodeEncodeBHist output,
        authorizedRecursorDecodeEncodeBHist authorization,
        authorizedRecursorDecodeEncodeBHist transports,
        authorizedRecursorDecodeEncodeBHist continuations,
        authorizedRecursorDecodeEncodeBHist provenance,
        authorizedRecursorDecodeEncodeBHist name]

private theorem authorizedRecursorToEventFlow_injective
    {x y : AuthorizedRecursorUp} :
    authorizedRecursorToEventFlow x =
      authorizedRecursorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      authorizedRecursorFromEventFlow (authorizedRecursorToEventFlow x) =
        authorizedRecursorFromEventFlow (authorizedRecursorToEventFlow y) :=
    congrArg authorizedRecursorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (authorizedRecursor_round_trip x).symm
      (Eq.trans hread (authorizedRecursor_round_trip y)))

private theorem authorizedRecursor_field_faithful :
    ∀ x y : AuthorizedRecursorUp,
      authorizedRecursorFields x = authorizedRecursorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk inductiveName signature motive branches output authorization transports continuations
      provenance name =>
      cases y with
      | mk inductiveName' signature' motive' branches' output' authorization' transports'
          continuations' provenance' name' =>
          cases hfields
          rfl

instance authorizedRecursorBHistCarrier :
    BHistCarrier AuthorizedRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := authorizedRecursorToEventFlow
  fromEventFlow := authorizedRecursorFromEventFlow

instance authorizedRecursorChapterTasteGate :
    ChapterTasteGate AuthorizedRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      authorizedRecursorFromEventFlow (authorizedRecursorToEventFlow x) = some x
    exact authorizedRecursor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (authorizedRecursorToEventFlow_injective heq)

instance authorizedRecursorFieldFaithful :
    FieldFaithful AuthorizedRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := authorizedRecursorFields
  field_faithful := authorizedRecursor_field_faithful

instance authorizedRecursorNontrivial :
    Nontrivial AuthorizedRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuthorizedRecursorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuthorizedRecursorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuthorizedRecursorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  authorizedRecursorChapterTasteGate

theorem AuthorizedRecursorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      authorizedRecursorDecodeBHist (authorizedRecursorEncodeBHist h) = h) ∧
      (∀ x : AuthorizedRecursorUp,
        authorizedRecursorFromEventFlow (authorizedRecursorToEventFlow x) =
          some x) ∧
        (∀ x y : AuthorizedRecursorUp,
          authorizedRecursorToEventFlow x =
            authorizedRecursorToEventFlow y → x = y) ∧
          authorizedRecursorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact authorizedRecursorDecodeEncodeBHist
  · constructor
    · exact authorizedRecursor_round_trip
    · constructor
      · intro x y heq
        exact authorizedRecursorToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuthorizedRecursorUp
