import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedSubstrateQuadrantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedSubstrateQuadrantUp : Type where
  | mk (substrate universality closure quadrant witness transports routes provenance
      nameCert : BHist) : ClosedSubstrateQuadrantUp
  deriving DecidableEq

private def closedSubstrateQuadrantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedSubstrateQuadrantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedSubstrateQuadrantEncodeBHist h

private def closedSubstrateQuadrantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedSubstrateQuadrantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedSubstrateQuadrantDecodeBHist tail)

private theorem closedSubstrateQuadrant_decode_encode_bhist :
    ∀ h : BHist,
      closedSubstrateQuadrantDecodeBHist (closedSubstrateQuadrantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def closedSubstrateQuadrantToEventFlow : ClosedSubstrateQuadrantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSubstrateQuadrantUp.mk substrate universality closure quadrant witness transports
      routes provenance nameCert =>
      [[BMark.b0],
        closedSubstrateQuadrantEncodeBHist substrate,
        [BMark.b1, BMark.b0],
        closedSubstrateQuadrantEncodeBHist universality,
        [BMark.b1, BMark.b1, BMark.b0],
        closedSubstrateQuadrantEncodeBHist closure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstrateQuadrantEncodeBHist quadrant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstrateQuadrantEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstrateQuadrantEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstrateQuadrantEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedSubstrateQuadrantEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedSubstrateQuadrantEncodeBHist nameCert]

private def closedSubstrateQuadrantFromEventFlow : EventFlow → Option ClosedSubstrateQuadrantUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | substrate :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | universality :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | closure :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | quadrant :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | witness :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (ClosedSubstrateQuadrantUp.mk
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    substrate)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    universality)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    closure)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    quadrant)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    witness)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    transports)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    routes)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    provenance)
                                                                                  (closedSubstrateQuadrantDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem closedSubstrateQuadrant_round_trip :
    ∀ x : ClosedSubstrateQuadrantUp,
      closedSubstrateQuadrantFromEventFlow (closedSubstrateQuadrantToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk substrate universality closure quadrant witness transports routes provenance
      nameCert =>
      change
        some
          (ClosedSubstrateQuadrantUp.mk
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist substrate))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist universality))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist closure))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist quadrant))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist witness))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist transports))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist routes))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist provenance))
            (closedSubstrateQuadrantDecodeBHist
              (closedSubstrateQuadrantEncodeBHist nameCert))) =
          some
            (ClosedSubstrateQuadrantUp.mk substrate universality closure quadrant witness
              transports routes provenance nameCert)
      rw [closedSubstrateQuadrant_decode_encode_bhist substrate,
        closedSubstrateQuadrant_decode_encode_bhist universality,
        closedSubstrateQuadrant_decode_encode_bhist closure,
        closedSubstrateQuadrant_decode_encode_bhist quadrant,
        closedSubstrateQuadrant_decode_encode_bhist witness,
        closedSubstrateQuadrant_decode_encode_bhist transports,
        closedSubstrateQuadrant_decode_encode_bhist routes,
        closedSubstrateQuadrant_decode_encode_bhist provenance,
        closedSubstrateQuadrant_decode_encode_bhist nameCert]

private theorem closedSubstrateQuadrantToEventFlow_injective
    {x y : ClosedSubstrateQuadrantUp} :
    closedSubstrateQuadrantToEventFlow x = closedSubstrateQuadrantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedSubstrateQuadrantFromEventFlow (closedSubstrateQuadrantToEventFlow x) =
        closedSubstrateQuadrantFromEventFlow (closedSubstrateQuadrantToEventFlow y) :=
    congrArg closedSubstrateQuadrantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedSubstrateQuadrant_round_trip x).symm
      (Eq.trans hread (closedSubstrateQuadrant_round_trip y)))

def closedSubstrateQuadrantFields :
    ClosedSubstrateQuadrantUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSubstrateQuadrantUp.mk substrate universality closure quadrant witness transports
      routes provenance nameCert =>
      [substrate, universality, closure, quadrant, witness, transports, routes, provenance,
        nameCert]

private theorem closedSubstrateQuadrant_field_faithful :
    ∀ x y : ClosedSubstrateQuadrantUp,
      closedSubstrateQuadrantFields x = closedSubstrateQuadrantFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk substrate universality closure quadrant witness transports routes provenance
      nameCert =>
      cases y with
      | mk substrate' universality' closure' quadrant' witness' transports' routes'
          provenance' nameCert' =>
          cases hfields
          rfl

instance closedSubstrateQuadrantBHistCarrier :
    BHistCarrier ClosedSubstrateQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedSubstrateQuadrantToEventFlow
  fromEventFlow := closedSubstrateQuadrantFromEventFlow

instance closedSubstrateQuadrantChapterTasteGate :
    ChapterTasteGate ClosedSubstrateQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedSubstrateQuadrantFromEventFlow
        (closedSubstrateQuadrantToEventFlow x) = some x
    exact closedSubstrateQuadrant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedSubstrateQuadrantToEventFlow_injective heq)

instance closedSubstrateQuadrantFieldFaithful :
    FieldFaithful ClosedSubstrateQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedSubstrateQuadrantFields
  field_faithful := closedSubstrateQuadrant_field_faithful

instance closedSubstrateQuadrantNontrivial :
    Nontrivial ClosedSubstrateQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedSubstrateQuadrantUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedSubstrateQuadrantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedSubstrateQuadrantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedSubstrateQuadrantChapterTasteGate

theorem ClosedSubstrateQuadrantTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClosedSubstrateQuadrantUp) ∧
      Nonempty (FieldFaithful ClosedSubstrateQuadrantUp) ∧
      Nonempty (Nontrivial ClosedSubstrateQuadrantUp) ∧
        (∀ h : BHist,
          closedSubstrateQuadrantDecodeBHist (closedSubstrateQuadrantEncodeBHist h) = h) ∧
          closedSubstrateQuadrantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨closedSubstrateQuadrantChapterTasteGate⟩, ⟨closedSubstrateQuadrantFieldFaithful⟩,
      ⟨closedSubstrateQuadrantNontrivial⟩, closedSubstrateQuadrant_decode_encode_bhist, rfl⟩

theorem ClosedSubstrateQuadrantCarrier_namecert_obligations
    (x : ClosedSubstrateQuadrantUp) :
    FieldFaithful.fields x = closedSubstrateQuadrantFields x ∧
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
        ∃ substrate universality closure quadrant witness transports routes provenance
            nameCert : BHist,
          x =
              ClosedSubstrateQuadrantUp.mk substrate universality closure quadrant witness
                transports routes provenance nameCert ∧
            closedSubstrateQuadrantFields x =
              [substrate, universality, closure, quadrant, witness, transports, routes,
                provenance, nameCert] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk substrate universality closure quadrant witness transports routes provenance nameCert =>
      constructor
      · rfl
      · constructor
        · change
            closedSubstrateQuadrantFromEventFlow
              (closedSubstrateQuadrantToEventFlow
                (ClosedSubstrateQuadrantUp.mk substrate universality closure quadrant witness
                  transports routes provenance nameCert)) =
              some
                (ClosedSubstrateQuadrantUp.mk substrate universality closure quadrant witness
                  transports routes provenance nameCert)
          exact
            closedSubstrateQuadrant_round_trip
              (ClosedSubstrateQuadrantUp.mk substrate universality closure quadrant witness
                transports routes provenance nameCert)
        · exact
            ⟨substrate, universality, closure, quadrant, witness, transports, routes,
              provenance, nameCert, rfl, rfl⟩

end BEDC.Derived.ClosedSubstrateQuadrantUp
