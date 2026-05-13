import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalLimitStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalLimitStabilityUp : Type where
  | mk :
      (source representative selector sealRow window transport route provenance name : BHist) →
        DiagonalLimitStabilityUp
  deriving DecidableEq

def diagonalLimitStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalLimitStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalLimitStabilityEncodeBHist h

def diagonalLimitStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalLimitStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalLimitStabilityDecodeBHist tail)

private theorem diagonalLimitStabilityDecode_encode_bhist :
    ∀ h : BHist, diagonalLimitStabilityDecodeBHist
      (diagonalLimitStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def diagonalLimitStabilityToEventFlow : DiagonalLimitStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalLimitStabilityUp.mk source representative selector sealRow window transport route
      provenance name =>
      [[BMark.b0],
        diagonalLimitStabilityEncodeBHist source,
        [BMark.b1, BMark.b0],
        diagonalLimitStabilityEncodeBHist representative,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitStabilityEncodeBHist selector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitStabilityEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitStabilityEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitStabilityEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitStabilityEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalLimitStabilityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        diagonalLimitStabilityEncodeBHist name]

def diagonalLimitStabilityFromEventFlow : EventFlow → Option DiagonalLimitStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | representative :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selector :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sealRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | window :: rest9 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (DiagonalLimitStabilityUp.mk
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    source)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    representative)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    selector)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    sealRow)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    window)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    transport)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    route)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    provenance)
                                                                                  (diagonalLimitStabilityDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem diagonalLimitStability_round_trip :
    ∀ x : DiagonalLimitStabilityUp,
      diagonalLimitStabilityFromEventFlow (diagonalLimitStabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source representative selector sealRow window transport route provenance name =>
      change
        some
          (DiagonalLimitStabilityUp.mk
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist source))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist representative))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist selector))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist sealRow))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist window))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist transport))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist route))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist provenance))
            (diagonalLimitStabilityDecodeBHist
              (diagonalLimitStabilityEncodeBHist name))) =
          some
            (DiagonalLimitStabilityUp.mk source representative selector sealRow window transport
              route provenance name)
      rw [diagonalLimitStabilityDecode_encode_bhist source,
        diagonalLimitStabilityDecode_encode_bhist representative,
        diagonalLimitStabilityDecode_encode_bhist selector,
        diagonalLimitStabilityDecode_encode_bhist sealRow,
        diagonalLimitStabilityDecode_encode_bhist window,
        diagonalLimitStabilityDecode_encode_bhist transport,
        diagonalLimitStabilityDecode_encode_bhist route,
        diagonalLimitStabilityDecode_encode_bhist provenance,
        diagonalLimitStabilityDecode_encode_bhist name]

private theorem diagonalLimitStabilityToEventFlow_injective
    {x y : DiagonalLimitStabilityUp} :
    diagonalLimitStabilityToEventFlow x = diagonalLimitStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalLimitStabilityFromEventFlow (diagonalLimitStabilityToEventFlow x) =
        diagonalLimitStabilityFromEventFlow (diagonalLimitStabilityToEventFlow y) :=
    congrArg diagonalLimitStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalLimitStability_round_trip x).symm
      (Eq.trans hread (diagonalLimitStability_round_trip y)))

instance diagonalLimitStabilityBHistCarrier : BHistCarrier DiagonalLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalLimitStabilityToEventFlow
  fromEventFlow := diagonalLimitStabilityFromEventFlow

instance diagonalLimitStabilityChapterTasteGate : ChapterTasteGate DiagonalLimitStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalLimitStabilityFromEventFlow (diagonalLimitStabilityToEventFlow x) =
      some x
    exact diagonalLimitStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalLimitStabilityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DiagonalLimitStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalLimitStabilityChapterTasteGate

instance diagonalLimitStabilityNontrivial : Nontrivial DiagonalLimitStabilityUp where
  witness_pair :=
    ⟨DiagonalLimitStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalLimitStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance diagonalLimitStabilityFieldFaithful : FieldFaithful DiagonalLimitStabilityUp where
  fields
    | DiagonalLimitStabilityUp.mk source representative selector sealRow window transport route
        provenance name =>
        [source, representative, selector, sealRow, window, transport, route, provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk source representative selector sealRow window transport route provenance name =>
        cases y with
        | mk source' representative' selector' sealRow' window' transport' route' provenance'
            name' =>
            injection hfields with hSource hTail0
            injection hTail0 with hRepresentative hTail1
            injection hTail1 with hSelector hTail2
            injection hTail2 with hSeal hTail3
            injection hTail3 with hWindow hTail4
            injection hTail4 with hTransport hTail5
            injection hTail5 with hRoute hTail6
            injection hTail6 with hProvenance hTail7
            injection hTail7 with hName _hNil
            cases hSource
            cases hRepresentative
            cases hSelector
            cases hSeal
            cases hWindow
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

theorem DiagonalLimitStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalLimitStabilityDecodeBHist
      (diagonalLimitStabilityEncodeBHist h) = h) ∧
      (∀ x : DiagonalLimitStabilityUp,
        diagonalLimitStabilityFromEventFlow (diagonalLimitStabilityToEventFlow x) =
          some x) ∧
        (∀ x y : DiagonalLimitStabilityUp,
          diagonalLimitStabilityToEventFlow x = diagonalLimitStabilityToEventFlow y → x = y) ∧
          (∀ x y : DiagonalLimitStabilityUp,
            FieldFaithful.fields x = FieldFaithful.fields y → x = y) ∧
            (∃ x y : DiagonalLimitStabilityUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diagonalLimitStabilityDecode_encode_bhist
  · constructor
    · exact diagonalLimitStability_round_trip
    · constructor
      · intro x y heq
        exact diagonalLimitStabilityToEventFlow_injective heq
      · constructor
        · exact FieldFaithful.field_faithful
        · exact
            ⟨diagonalLimitStabilityNontrivial.witness_pair.1,
              diagonalLimitStabilityNontrivial.witness_pair.2.1,
              diagonalLimitStabilityNontrivial.witness_pair.2.2⟩

end BEDC.Derived.DiagonalLimitStabilityUp
