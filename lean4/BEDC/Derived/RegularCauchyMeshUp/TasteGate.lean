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
      (request meshIndex streamWindow regseqReadback tolerance meshCompatibility realHandoff
        transports routes provenance name : BHist) →
      RegularCauchyMeshUp

private def regularCauchyMeshEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMeshEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMeshEncodeBHist h

private def regularCauchyMeshDecodeBHist : RawEvent → BHist
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
    {request request' meshIndex meshIndex' streamWindow streamWindow' regseqReadback
      regseqReadback' tolerance tolerance' meshCompatibility meshCompatibility' realHandoff
      realHandoff' transports transports' routes routes' provenance provenance' name name' : BHist}
    (hRequest : request' = request)
    (hMeshIndex : meshIndex' = meshIndex)
    (hStreamWindow : streamWindow' = streamWindow)
    (hRegseqReadback : regseqReadback' = regseqReadback)
    (hTolerance : tolerance' = tolerance)
    (hMeshCompatibility : meshCompatibility' = meshCompatibility)
    (hRealHandoff : realHandoff' = realHandoff)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RegularCauchyMeshUp.mk request' meshIndex' streamWindow' regseqReadback' tolerance'
        meshCompatibility' realHandoff' transports' routes' provenance' name' =
      RegularCauchyMeshUp.mk request meshIndex streamWindow regseqReadback tolerance
        meshCompatibility realHandoff transports routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRequest
  cases hMeshIndex
  cases hStreamWindow
  cases hRegseqReadback
  cases hTolerance
  cases hMeshCompatibility
  cases hRealHandoff
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

private def regularCauchyMeshToEventFlow : RegularCauchyMeshUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMeshUp.mk request meshIndex streamWindow regseqReadback tolerance
      meshCompatibility realHandoff transports routes provenance name =>
      [[BMark.b0],
        regularCauchyMeshEncodeBHist request,
        [BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist meshIndex,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist streamWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist regseqReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist meshCompatibility,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist realHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyMeshEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMeshEncodeBHist name]

private def regularCauchyMeshFromEventFlow : EventFlow → Option RegularCauchyMeshUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | meshIndex :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | streamWindow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | regseqReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | tolerance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | meshCompatibility :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | realHandoff :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transports :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes :: rest17 =>
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
                                                                                                (RegularCauchyMeshUp.mk
                                                                                                  (regularCauchyMeshDecodeBHist request)
                                                                                                  (regularCauchyMeshDecodeBHist meshIndex)
                                                                                                  (regularCauchyMeshDecodeBHist streamWindow)
                                                                                                  (regularCauchyMeshDecodeBHist regseqReadback)
                                                                                                  (regularCauchyMeshDecodeBHist tolerance)
                                                                                                  (regularCauchyMeshDecodeBHist meshCompatibility)
                                                                                                  (regularCauchyMeshDecodeBHist realHandoff)
                                                                                                  (regularCauchyMeshDecodeBHist transports)
                                                                                                  (regularCauchyMeshDecodeBHist routes)
                                                                                                  (regularCauchyMeshDecodeBHist provenance)
                                                                                                  (regularCauchyMeshDecodeBHist name))
                                                                                          | _ :: _ => none

private theorem regularCauchyMesh_round_trip :
    ∀ x : RegularCauchyMeshUp,
      regularCauchyMeshFromEventFlow (regularCauchyMeshToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request meshIndex streamWindow regseqReadback tolerance meshCompatibility realHandoff
      transports routes provenance name =>
      change
        some
          (RegularCauchyMeshUp.mk
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist request))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist meshIndex))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist streamWindow))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist regseqReadback))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist tolerance))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist meshCompatibility))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist realHandoff))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist transports))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist routes))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist provenance))
            (regularCauchyMeshDecodeBHist (regularCauchyMeshEncodeBHist name))) =
          some
            (RegularCauchyMeshUp.mk request meshIndex streamWindow regseqReadback tolerance
              meshCompatibility realHandoff transports routes provenance name)
      exact
        congrArg some
          (regularCauchyMesh_mk_congr
            (regularCauchyMeshDecode_encode_bhist request)
            (regularCauchyMeshDecode_encode_bhist meshIndex)
            (regularCauchyMeshDecode_encode_bhist streamWindow)
            (regularCauchyMeshDecode_encode_bhist regseqReadback)
            (regularCauchyMeshDecode_encode_bhist tolerance)
            (regularCauchyMeshDecode_encode_bhist meshCompatibility)
            (regularCauchyMeshDecode_encode_bhist realHandoff)
            (regularCauchyMeshDecode_encode_bhist transports)
            (regularCauchyMeshDecode_encode_bhist routes)
            (regularCauchyMeshDecode_encode_bhist provenance)
            (regularCauchyMeshDecode_encode_bhist name))

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

theorem RegularCauchyMeshTasteGate_single_carrier_alignment :
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
