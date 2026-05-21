import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniversalityClosureQuadrantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniversalityClosureQuadrantUp : Type where
  | mk (substrate universality closure quadrant witness transports routes provenance name : BHist) :
      UniversalityClosureQuadrantUp
  deriving DecidableEq

def universalityClosureQuadrantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: universalityClosureQuadrantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: universalityClosureQuadrantEncodeBHist h

def universalityClosureQuadrantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (universalityClosureQuadrantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (universalityClosureQuadrantDecodeBHist tail)

private theorem universalityClosureQuadrant_decode_encode_bhist :
    ∀ h : BHist,
      universalityClosureQuadrantDecodeBHist
        (universalityClosureQuadrantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def universalityClosureQuadrantToEventFlow :
    UniversalityClosureQuadrantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniversalityClosureQuadrantUp.mk substrate universality closure quadrant witness
      transports routes provenance name =>
      [[BMark.b0],
        universalityClosureQuadrantEncodeBHist substrate,
        [BMark.b1, BMark.b0],
        universalityClosureQuadrantEncodeBHist universality,
        [BMark.b1, BMark.b1, BMark.b0],
        universalityClosureQuadrantEncodeBHist closure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalityClosureQuadrantEncodeBHist quadrant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalityClosureQuadrantEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalityClosureQuadrantEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalityClosureQuadrantEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        universalityClosureQuadrantEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        universalityClosureQuadrantEncodeBHist name]

private def universalityClosureQuadrantDecodePacket
    (substrate universality closure quadrant witness transports routes provenance name :
      RawEvent) : UniversalityClosureQuadrantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  UniversalityClosureQuadrantUp.mk
    (universalityClosureQuadrantDecodeBHist substrate)
    (universalityClosureQuadrantDecodeBHist universality)
    (universalityClosureQuadrantDecodeBHist closure)
    (universalityClosureQuadrantDecodeBHist quadrant)
    (universalityClosureQuadrantDecodeBHist witness)
    (universalityClosureQuadrantDecodeBHist transports)
    (universalityClosureQuadrantDecodeBHist routes)
    (universalityClosureQuadrantDecodeBHist provenance)
    (universalityClosureQuadrantDecodeBHist name)

def universalityClosureQuadrantFromEventFlow :
    EventFlow → Option UniversalityClosureQuadrantUp
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
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (universalityClosureQuadrantDecodePacket
                                                                                  substrate
                                                                                  universality
                                                                                  closure
                                                                                  quadrant
                                                                                  witness
                                                                                  transports
                                                                                  routes
                                                                                  provenance
                                                                                  name)
                                                                          | _ :: _ => none

private theorem universalityClosureQuadrant_round_trip :
    ∀ x : UniversalityClosureQuadrantUp,
      universalityClosureQuadrantFromEventFlow
        (universalityClosureQuadrantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk substrate universality closure quadrant witness transports routes provenance name =>
      change
        some
          (universalityClosureQuadrantDecodePacket
            (universalityClosureQuadrantEncodeBHist substrate)
            (universalityClosureQuadrantEncodeBHist universality)
            (universalityClosureQuadrantEncodeBHist closure)
            (universalityClosureQuadrantEncodeBHist quadrant)
            (universalityClosureQuadrantEncodeBHist witness)
            (universalityClosureQuadrantEncodeBHist transports)
            (universalityClosureQuadrantEncodeBHist routes)
            (universalityClosureQuadrantEncodeBHist provenance)
            (universalityClosureQuadrantEncodeBHist name)) =
          some
            (UniversalityClosureQuadrantUp.mk substrate universality closure quadrant witness
              transports routes provenance name)
      unfold universalityClosureQuadrantDecodePacket
      rw [universalityClosureQuadrant_decode_encode_bhist substrate,
        universalityClosureQuadrant_decode_encode_bhist universality,
        universalityClosureQuadrant_decode_encode_bhist closure,
        universalityClosureQuadrant_decode_encode_bhist quadrant,
        universalityClosureQuadrant_decode_encode_bhist witness,
        universalityClosureQuadrant_decode_encode_bhist transports,
        universalityClosureQuadrant_decode_encode_bhist routes,
        universalityClosureQuadrant_decode_encode_bhist provenance,
        universalityClosureQuadrant_decode_encode_bhist name]

private theorem universalityClosureQuadrantToEventFlow_injective
    {x y : UniversalityClosureQuadrantUp} :
    universalityClosureQuadrantToEventFlow x =
      universalityClosureQuadrantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      universalityClosureQuadrantFromEventFlow
          (universalityClosureQuadrantToEventFlow x) =
        universalityClosureQuadrantFromEventFlow
          (universalityClosureQuadrantToEventFlow y) :=
    congrArg universalityClosureQuadrantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (universalityClosureQuadrant_round_trip x).symm
      (Eq.trans hread (universalityClosureQuadrant_round_trip y)))

private def universalityClosureQuadrantFields :
    UniversalityClosureQuadrantUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniversalityClosureQuadrantUp.mk substrate universality closure quadrant witness
      transports routes provenance name =>
      [substrate, universality, closure, quadrant, witness, transports, routes, provenance,
        name]

private theorem universalityClosureQuadrant_field_faithful :
    ∀ x y : UniversalityClosureQuadrantUp,
      universalityClosureQuadrantFields x =
        universalityClosureQuadrantFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk substrate universality closure quadrant witness transports routes provenance name =>
      cases y with
      | mk substrate' universality' closure' quadrant' witness' transports' routes'
          provenance' name' =>
          cases hfields
          rfl

instance universalityClosureQuadrantBHistCarrier :
    BHistCarrier UniversalityClosureQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := universalityClosureQuadrantToEventFlow
  fromEventFlow := universalityClosureQuadrantFromEventFlow

instance universalityClosureQuadrantChapterTasteGate :
    ChapterTasteGate UniversalityClosureQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      universalityClosureQuadrantFromEventFlow
        (universalityClosureQuadrantToEventFlow x) = some x
    exact universalityClosureQuadrant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (universalityClosureQuadrantToEventFlow_injective heq)

instance universalityClosureQuadrantFieldFaithful :
    FieldFaithful UniversalityClosureQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := universalityClosureQuadrantFields
  field_faithful := universalityClosureQuadrant_field_faithful

instance universalityClosureQuadrantNontrivial :
    Nontrivial UniversalityClosureQuadrantUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniversalityClosureQuadrantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniversalityClosureQuadrantUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniversalityClosureQuadrantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  universalityClosureQuadrantChapterTasteGate

theorem UniversalityClosureQuadrantTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniversalityClosureQuadrantUp) ∧
      Nonempty (FieldFaithful UniversalityClosureQuadrantUp) ∧
        Nonempty (Nontrivial UniversalityClosureQuadrantUp) ∧
          (∀ h : BHist,
            universalityClosureQuadrantDecodeBHist
              (universalityClosureQuadrantEncodeBHist h) = h) ∧
            (∀ x : UniversalityClosureQuadrantUp,
              universalityClosureQuadrantFromEventFlow
                (universalityClosureQuadrantToEventFlow x) = some x) ∧
              (∀ x y : UniversalityClosureQuadrantUp,
                universalityClosureQuadrantToEventFlow x =
                    universalityClosureQuadrantToEventFlow y →
                  x = y) ∧
                universalityClosureQuadrantEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨universalityClosureQuadrantChapterTasteGate⟩,
      ⟨universalityClosureQuadrantFieldFaithful⟩,
      ⟨universalityClosureQuadrantNontrivial⟩,
      universalityClosureQuadrant_decode_encode_bhist,
      universalityClosureQuadrant_round_trip,
      (fun _ _ heq => universalityClosureQuadrantToEventFlow_injective heq),
      rfl⟩

theorem UniversalityClosureQuadrant_axis_independence
    (x : UniversalityClosureQuadrantUp) :
    ∃ S U K G W H C P N : BHist,
      x = UniversalityClosureQuadrantUp.mk S U K G W H C P N ∧
        universalityClosureQuadrantToEventFlow x =
          [[BMark.b0],
            universalityClosureQuadrantEncodeBHist S,
            [BMark.b1, BMark.b0],
            universalityClosureQuadrantEncodeBHist U,
            [BMark.b1, BMark.b1, BMark.b0],
            universalityClosureQuadrantEncodeBHist K,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            universalityClosureQuadrantEncodeBHist G,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            universalityClosureQuadrantEncodeBHist W,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            universalityClosureQuadrantEncodeBHist H,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            universalityClosureQuadrantEncodeBHist C,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            universalityClosureQuadrantEncodeBHist P,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0],
            universalityClosureQuadrantEncodeBHist N] ∧
          hsame U U ∧ hsame K K := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  cases x with
  | mk S U K G W H C P N =>
      exact ⟨S, U, K, G, W, H, C, P, N, rfl, rfl, hsame_refl U, hsame_refl K⟩

end BEDC.Derived.UniversalityClosureQuadrantUp
