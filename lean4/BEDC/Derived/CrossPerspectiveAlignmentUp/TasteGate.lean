import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CrossPerspectiveAlignmentUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CrossPerspectiveAlignmentUp : Type where
  | mk :
      (source target locality commitment multiHist transports routes provenance nameCert :
        BHist) →
        CrossPerspectiveAlignmentUp
  deriving DecidableEq

def crossPerspectiveAlignmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: crossPerspectiveAlignmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: crossPerspectiveAlignmentEncodeBHist h

def crossPerspectiveAlignmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (crossPerspectiveAlignmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (crossPerspectiveAlignmentDecodeBHist tail)

private theorem crossPerspectiveAlignment_decode_encode_bhist :
    ∀ h : BHist,
      crossPerspectiveAlignmentDecodeBHist (crossPerspectiveAlignmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def crossPerspectiveAlignmentToEventFlow : CrossPerspectiveAlignmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CrossPerspectiveAlignmentUp.mk source target locality commitment multiHist transports routes
      provenance nameCert =>
      [[BMark.b0],
        crossPerspectiveAlignmentEncodeBHist source,
        [BMark.b1, BMark.b0],
        crossPerspectiveAlignmentEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        crossPerspectiveAlignmentEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossPerspectiveAlignmentEncodeBHist commitment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossPerspectiveAlignmentEncodeBHist multiHist,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossPerspectiveAlignmentEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        crossPerspectiveAlignmentEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        crossPerspectiveAlignmentEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        crossPerspectiveAlignmentEncodeBHist nameCert]

def crossPerspectiveAlignmentFromEventFlow : EventFlow → Option CrossPerspectiveAlignmentUp
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
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | locality :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | commitment :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | multiHist :: rest9 =>
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
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (CrossPerspectiveAlignmentUp.mk
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    source)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    target)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    locality)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    commitment)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    multiHist)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    transports)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    routes)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    provenance)
                                                                                  (crossPerspectiveAlignmentDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ =>
                                                                              none

private theorem crossPerspectiveAlignment_round_trip :
    ∀ x : CrossPerspectiveAlignmentUp,
      crossPerspectiveAlignmentFromEventFlow (crossPerspectiveAlignmentToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target locality commitment multiHist transports routes provenance nameCert =>
      change
        some
          (CrossPerspectiveAlignmentUp.mk
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist source))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist target))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist locality))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist commitment))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist multiHist))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist transports))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist routes))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist provenance))
            (crossPerspectiveAlignmentDecodeBHist
              (crossPerspectiveAlignmentEncodeBHist nameCert))) =
          some
            (CrossPerspectiveAlignmentUp.mk source target locality commitment multiHist
              transports routes provenance nameCert)
      rw [crossPerspectiveAlignment_decode_encode_bhist source,
        crossPerspectiveAlignment_decode_encode_bhist target,
        crossPerspectiveAlignment_decode_encode_bhist locality,
        crossPerspectiveAlignment_decode_encode_bhist commitment,
        crossPerspectiveAlignment_decode_encode_bhist multiHist,
        crossPerspectiveAlignment_decode_encode_bhist transports,
        crossPerspectiveAlignment_decode_encode_bhist routes,
        crossPerspectiveAlignment_decode_encode_bhist provenance,
        crossPerspectiveAlignment_decode_encode_bhist nameCert]

private theorem crossPerspectiveAlignmentToEventFlow_injective {x y : CrossPerspectiveAlignmentUp} :
    crossPerspectiveAlignmentToEventFlow x = crossPerspectiveAlignmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      crossPerspectiveAlignmentFromEventFlow (crossPerspectiveAlignmentToEventFlow x) =
        crossPerspectiveAlignmentFromEventFlow (crossPerspectiveAlignmentToEventFlow y) :=
    congrArg crossPerspectiveAlignmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (crossPerspectiveAlignment_round_trip x).symm
      (Eq.trans hread (crossPerspectiveAlignment_round_trip y)))

instance crossPerspectiveAlignmentBHistCarrier : BHistCarrier CrossPerspectiveAlignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := crossPerspectiveAlignmentToEventFlow
  fromEventFlow := crossPerspectiveAlignmentFromEventFlow

instance crossPerspectiveAlignmentChapterTasteGate :
    ChapterTasteGate CrossPerspectiveAlignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      crossPerspectiveAlignmentFromEventFlow (crossPerspectiveAlignmentToEventFlow x) =
        some x
    exact crossPerspectiveAlignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (crossPerspectiveAlignmentToEventFlow_injective heq)

theorem CrossPerspectiveAlignmentTasteGate_single_carrier_alignment :
    (forall h : BHist,
      crossPerspectiveAlignmentDecodeBHist (crossPerspectiveAlignmentEncodeBHist h) = h) /\
      (forall x : CrossPerspectiveAlignmentUp,
        crossPerspectiveAlignmentFromEventFlow (crossPerspectiveAlignmentToEventFlow x) =
          some x) /\
      (forall x y : CrossPerspectiveAlignmentUp,
        crossPerspectiveAlignmentToEventFlow x = crossPerspectiveAlignmentToEventFlow y ->
          x = y) /\
        crossPerspectiveAlignmentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨crossPerspectiveAlignment_decode_encode_bhist, crossPerspectiveAlignment_round_trip,
      fun _x _y heq => crossPerspectiveAlignmentToEventFlow_injective heq, rfl⟩

end BEDC.Derived.CrossPerspectiveAlignmentUp
