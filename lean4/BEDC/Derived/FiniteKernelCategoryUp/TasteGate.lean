import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteKernelCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteKernelCategoryUp : Type where
  | mk :
      (objectRow homRow identityRow compositionRow associativityRow unitRow transportRow
        routeRow provenanceRow nameCertRow : BHist) →
      FiniteKernelCategoryUp
  deriving DecidableEq

def finiteKernelCategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteKernelCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteKernelCategoryEncodeBHist h

def finiteKernelCategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteKernelCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteKernelCategoryDecodeBHist tail)

private theorem finiteKernelCategoryDecode_encode_bhist :
    ∀ h : BHist, finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem finiteKernelCategory_mk_congr
    {objectRow objectRow' homRow homRow' identityRow identityRow' compositionRow
      compositionRow' associativityRow associativityRow' unitRow unitRow' transportRow
      transportRow' routeRow routeRow' provenanceRow provenanceRow' nameCertRow
      nameCertRow' : BHist}
    (hObject : objectRow' = objectRow)
    (hHom : homRow' = homRow)
    (hIdentity : identityRow' = identityRow)
    (hComposition : compositionRow' = compositionRow)
    (hAssociativity : associativityRow' = associativityRow)
    (hUnit : unitRow' = unitRow)
    (hTransport : transportRow' = transportRow)
    (hRoute : routeRow' = routeRow)
    (hProvenance : provenanceRow' = provenanceRow)
    (hNameCert : nameCertRow' = nameCertRow) :
    FiniteKernelCategoryUp.mk objectRow' homRow' identityRow' compositionRow'
        associativityRow' unitRow' transportRow' routeRow' provenanceRow' nameCertRow' =
      FiniteKernelCategoryUp.mk objectRow homRow identityRow compositionRow associativityRow
        unitRow transportRow routeRow provenanceRow nameCertRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hObject
  cases hHom
  cases hIdentity
  cases hComposition
  cases hAssociativity
  cases hUnit
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

def finiteKernelCategoryToEventFlow : FiniteKernelCategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteKernelCategoryUp.mk objectRow homRow identityRow compositionRow associativityRow
      unitRow transportRow routeRow provenanceRow nameCertRow =>
      [[BMark.b0],
        finiteKernelCategoryEncodeBHist objectRow,
        [BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist homRow,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist identityRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist compositionRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist associativityRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist unitRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist routeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteKernelCategoryEncodeBHist provenanceRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteKernelCategoryEncodeBHist nameCertRow]

def finiteKernelCategoryFromEventFlow : EventFlow → Option FiniteKernelCategoryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | objectRow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | homRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | identityRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | compositionRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | associativityRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | unitRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transportRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routeRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenanceRow ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] => none
                                                                              | nameCertRow ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (FiniteKernelCategoryUp.mk
                                                                                          (finiteKernelCategoryDecodeBHist objectRow)
                                                                                          (finiteKernelCategoryDecodeBHist homRow)
                                                                                          (finiteKernelCategoryDecodeBHist identityRow)
                                                                                          (finiteKernelCategoryDecodeBHist compositionRow)
                                                                                          (finiteKernelCategoryDecodeBHist associativityRow)
                                                                                          (finiteKernelCategoryDecodeBHist unitRow)
                                                                                          (finiteKernelCategoryDecodeBHist transportRow)
                                                                                          (finiteKernelCategoryDecodeBHist routeRow)
                                                                                          (finiteKernelCategoryDecodeBHist provenanceRow)
                                                                                          (finiteKernelCategoryDecodeBHist nameCertRow))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem finiteKernelCategory_round_trip :
    ∀ x : FiniteKernelCategoryUp,
      finiteKernelCategoryFromEventFlow (finiteKernelCategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk objectRow homRow identityRow compositionRow associativityRow unitRow transportRow
      routeRow provenanceRow nameCertRow =>
      change
        some
          (FiniteKernelCategoryUp.mk
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist objectRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist homRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist identityRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist compositionRow))
            (finiteKernelCategoryDecodeBHist
              (finiteKernelCategoryEncodeBHist associativityRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist unitRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist transportRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist routeRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist provenanceRow))
            (finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist nameCertRow))) =
          some
            (FiniteKernelCategoryUp.mk objectRow homRow identityRow compositionRow
              associativityRow unitRow transportRow routeRow provenanceRow nameCertRow)
      exact
        congrArg some
          (finiteKernelCategory_mk_congr
            (finiteKernelCategoryDecode_encode_bhist objectRow)
            (finiteKernelCategoryDecode_encode_bhist homRow)
            (finiteKernelCategoryDecode_encode_bhist identityRow)
            (finiteKernelCategoryDecode_encode_bhist compositionRow)
            (finiteKernelCategoryDecode_encode_bhist associativityRow)
            (finiteKernelCategoryDecode_encode_bhist unitRow)
            (finiteKernelCategoryDecode_encode_bhist transportRow)
            (finiteKernelCategoryDecode_encode_bhist routeRow)
            (finiteKernelCategoryDecode_encode_bhist provenanceRow)
            (finiteKernelCategoryDecode_encode_bhist nameCertRow))

private theorem finiteKernelCategoryToEventFlow_injective {x y : FiniteKernelCategoryUp} :
    finiteKernelCategoryToEventFlow x = finiteKernelCategoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteKernelCategoryFromEventFlow (finiteKernelCategoryToEventFlow x) =
        finiteKernelCategoryFromEventFlow (finiteKernelCategoryToEventFlow y) :=
    congrArg finiteKernelCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteKernelCategory_round_trip x).symm
      (Eq.trans hread (finiteKernelCategory_round_trip y)))

instance finiteKernelCategoryBHistCarrier : BHistCarrier FiniteKernelCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteKernelCategoryToEventFlow
  fromEventFlow := finiteKernelCategoryFromEventFlow

instance finiteKernelCategoryChapterTasteGate : ChapterTasteGate FiniteKernelCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteKernelCategoryFromEventFlow (finiteKernelCategoryToEventFlow x) = some x
    exact finiteKernelCategory_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteKernelCategoryToEventFlow_injective heq)

theorem FiniteKernelCategoryTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteKernelCategoryDecodeBHist (finiteKernelCategoryEncodeBHist h) = h) ∧
      (∀ x : FiniteKernelCategoryUp,
        finiteKernelCategoryFromEventFlow (finiteKernelCategoryToEventFlow x) = some x) ∧
        (∀ x y : FiniteKernelCategoryUp,
          finiteKernelCategoryToEventFlow x = finiteKernelCategoryToEventFlow y → x = y) ∧
          finiteKernelCategoryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteKernelCategoryDecode_encode_bhist
  · constructor
    · exact finiteKernelCategory_round_trip
    · constructor
      · intro x y heq
        exact finiteKernelCategoryToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteKernelCategoryUp
