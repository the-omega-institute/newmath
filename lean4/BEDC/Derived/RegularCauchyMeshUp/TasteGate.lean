import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMeshUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMeshUp : Type where
  | mk :
      (mesh modulus index lower upper diameter refinement cauchy regular witness provenance :
        BHist) →
      RegularCauchyMeshUp
  deriving DecidableEq

def regularCauchyMeshEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMeshEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMeshEncodeBHist h

def regularCauchyMeshDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMeshDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMeshDecodeBHist tail)

private theorem regularCauchyMeshDecode_encode_bhist :
    ∀ h : BHist, regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyMesh_mk_congr
    {mesh mesh' modulus modulus' index index' lower lower' upper upper' diameter diameter'
      refinement refinement' cauchy cauchy' regular regular' witness witness' provenance
      provenance' : BHist}
    (hMesh : mesh' = mesh)
    (hModulus : modulus' = modulus)
    (hIndex : index' = index)
    (hLower : lower' = lower)
    (hUpper : upper' = upper)
    (hDiameter : diameter' = diameter)
    (hRefinement : refinement' = refinement)
    (hCauchy : cauchy' = cauchy)
    (hRegular : regular' = regular)
    (hWitness : witness' = witness)
    (hProvenance : provenance' = provenance) :
    RegularCauchyMeshUp.mk mesh' modulus' index' lower' upper' diameter' refinement'
        cauchy' regular' witness' provenance' =
      RegularCauchyMeshUp.mk mesh modulus index lower upper diameter refinement cauchy regular
        witness provenance := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMesh
  cases hModulus
  cases hIndex
  cases hLower
  cases hUpper
  cases hDiameter
  cases hRefinement
  cases hCauchy
  cases hRegular
  cases hWitness
  cases hProvenance
  rfl

def regularCauchyMeshToEventFlow : RegularCauchyMeshUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMeshUp.mk mesh modulus index lower upper diameter refinement cauchy regular
      witness provenance =>
      [[BMark.b0],
        regularCauchyMeshEncodeBHist mesh,
        [BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist index,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist lower,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist upper,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist diameter,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist refinement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyMeshEncodeBHist cauchy,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist provenance]

def regularCauchyMeshFromEventFlow : EventFlow → Option RegularCauchyMeshUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | mesh :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | index :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | lower :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | upper :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | diameter :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | refinement :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | cauchy :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | regular :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | witness ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] =>
                                                                                          none
                                                                                      | provenance ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (RegularCauchyMeshUp.mk
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    mesh)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    modulus)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    index)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    lower)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    upper)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    diameter)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    refinement)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    cauchy)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    regular)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    witness)
                                                                                                  (regularCauchyMeshDecodeBHist
                                                                                                    provenance))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem regularCauchyMesh_round_trip :
    ∀ x : RegularCauchyMeshUp,
      regularCauchyMeshFromEventFlow (regularCauchyMeshToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk mesh modulus index lower upper diameter refinement cauchy regular witness provenance =>
      change
        some
          (RegularCauchyMeshUp.mk
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist mesh))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist modulus))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist index))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist lower))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist upper))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist diameter))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist refinement))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist cauchy))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist regular))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist witness))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist provenance))) =
          some
            (RegularCauchyMeshUp.mk mesh modulus index lower upper diameter refinement cauchy
              regular witness provenance)
      exact
        congrArg some
          (regularCauchyMesh_mk_congr
            (regularCauchyMeshDecode_encode_bhist mesh)
            (regularCauchyMeshDecode_encode_bhist modulus)
            (regularCauchyMeshDecode_encode_bhist index)
            (regularCauchyMeshDecode_encode_bhist lower)
            (regularCauchyMeshDecode_encode_bhist upper)
            (regularCauchyMeshDecode_encode_bhist diameter)
            (regularCauchyMeshDecode_encode_bhist refinement)
            (regularCauchyMeshDecode_encode_bhist cauchy)
            (regularCauchyMeshDecode_encode_bhist regular)
            (regularCauchyMeshDecode_encode_bhist witness)
            (regularCauchyMeshDecode_encode_bhist provenance))

private theorem regularCauchyMeshToEventFlow_injective {x y : RegularCauchyMeshUp} :
    regularCauchyMeshToEventFlow x = regularCauchyMeshToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMeshFromEventFlow (regularCauchyMeshToEventFlow x) =
        regularCauchyMeshFromEventFlow (regularCauchyMeshToEventFlow y) :=
    congrArg regularCauchyMeshFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyMesh_round_trip x).symm
      (Eq.trans hread (regularCauchyMesh_round_trip y)))

instance regularCauchyMeshBHistCarrier : BHistCarrier RegularCauchyMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMeshToEventFlow
  fromEventFlow := regularCauchyMeshFromEventFlow

instance regularCauchyMeshChapterTasteGate : ChapterTasteGate RegularCauchyMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMeshFromEventFlow (regularCauchyMeshToEventFlow x) = some x
    exact regularCauchyMesh_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMeshToEventFlow_injective heq)

theorem RegularCauchyMeshCarrier_namecert_obligations :
    (∀ h : BHist, regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMeshUp,
        regularCauchyMeshFromEventFlow (regularCauchyMeshToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyMeshUp,
          regularCauchyMeshToEventFlow x = regularCauchyMeshToEventFlow y → x = y) ∧
          regularCauchyMeshEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyMeshDecode_encode_bhist
  · constructor
    · exact regularCauchyMesh_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyMeshToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyMeshUp
