import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContourSumWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContourSumWindowUp : Type where
  | mk :
      (contour holomorphic subdivision riemann output transport continuation provenance name :
        BHist) →
      ContourSumWindowUp
  deriving DecidableEq

private def contourSumWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contourSumWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contourSumWindowEncodeBHist h

private def contourSumWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contourSumWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contourSumWindowDecodeBHist tail)

private theorem contourSumWindowDecode_encode_bhist :
    ∀ h : BHist, contourSumWindowDecodeBHist (contourSumWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem contourSumWindow_mk_congr
    {contour contour' holomorphic holomorphic' subdivision subdivision' riemann riemann'
      output output' transport transport' continuation continuation' provenance provenance'
      name name' : BHist}
    (hContour : contour' = contour)
    (hHolomorphic : holomorphic' = holomorphic)
    (hSubdivision : subdivision' = subdivision)
    (hRiemann : riemann' = riemann)
    (hOutput : output' = output)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ContourSumWindowUp.mk contour' holomorphic' subdivision' riemann' output' transport'
        continuation' provenance' name' =
      ContourSumWindowUp.mk contour holomorphic subdivision riemann output transport
        continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hContour
  cases hHolomorphic
  cases hSubdivision
  cases hRiemann
  cases hOutput
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

private def contourSumWindowToEventFlow : ContourSumWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContourSumWindowUp.mk contour holomorphic subdivision riemann output transport
      continuation provenance name =>
      [[BMark.b0],
        contourSumWindowEncodeBHist contour,
        [BMark.b1, BMark.b0],
        contourSumWindowEncodeBHist holomorphic,
        [BMark.b1, BMark.b1, BMark.b0],
        contourSumWindowEncodeBHist subdivision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourSumWindowEncodeBHist riemann,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourSumWindowEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourSumWindowEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        contourSumWindowEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        contourSumWindowEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        contourSumWindowEncodeBHist name]

private def contourSumWindowFromEventFlow : EventFlow → Option ContourSumWindowUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | contour :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | holomorphic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | subdivision :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | riemann :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | output :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                                (ContourSumWindowUp.mk
                                                                                  (contourSumWindowDecodeBHist contour)
                                                                                  (contourSumWindowDecodeBHist holomorphic)
                                                                                  (contourSumWindowDecodeBHist subdivision)
                                                                                  (contourSumWindowDecodeBHist riemann)
                                                                                  (contourSumWindowDecodeBHist output)
                                                                                  (contourSumWindowDecodeBHist transport)
                                                                                  (contourSumWindowDecodeBHist continuation)
                                                                                  (contourSumWindowDecodeBHist provenance)
                                                                                  (contourSumWindowDecodeBHist name))
                                                                          | _ :: _ => none

private theorem contourSumWindow_round_trip :
    ∀ x : ContourSumWindowUp,
      contourSumWindowFromEventFlow (contourSumWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk contour holomorphic subdivision riemann output transport continuation provenance name =>
      change
        some
          (ContourSumWindowUp.mk
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist contour))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist holomorphic))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist subdivision))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist riemann))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist output))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist transport))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist continuation))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist provenance))
            (contourSumWindowDecodeBHist (contourSumWindowEncodeBHist name))) =
          some
            (ContourSumWindowUp.mk contour holomorphic subdivision riemann output transport
              continuation provenance name)
      exact
        congrArg some
          (contourSumWindow_mk_congr
            (contourSumWindowDecode_encode_bhist contour)
            (contourSumWindowDecode_encode_bhist holomorphic)
            (contourSumWindowDecode_encode_bhist subdivision)
            (contourSumWindowDecode_encode_bhist riemann)
            (contourSumWindowDecode_encode_bhist output)
            (contourSumWindowDecode_encode_bhist transport)
            (contourSumWindowDecode_encode_bhist continuation)
            (contourSumWindowDecode_encode_bhist provenance)
            (contourSumWindowDecode_encode_bhist name))

private theorem contourSumWindowToEventFlow_injective {x y : ContourSumWindowUp} :
    contourSumWindowToEventFlow x = contourSumWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contourSumWindowFromEventFlow (contourSumWindowToEventFlow x) =
        contourSumWindowFromEventFlow (contourSumWindowToEventFlow y) :=
    congrArg contourSumWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (contourSumWindow_round_trip x).symm
      (Eq.trans hread (contourSumWindow_round_trip y)))

instance contourSumWindowBHistCarrier : BHistCarrier ContourSumWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contourSumWindowToEventFlow
  fromEventFlow := contourSumWindowFromEventFlow

instance contourSumWindowChapterTasteGate : ChapterTasteGate ContourSumWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contourSumWindowFromEventFlow (contourSumWindowToEventFlow x) = some x
    exact contourSumWindow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contourSumWindowToEventFlow_injective heq)

theorem ContourSumWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist, contourSumWindowDecodeBHist (contourSumWindowEncodeBHist h) = h) ∧
      (∀ x : ContourSumWindowUp,
        contourSumWindowFromEventFlow (contourSumWindowToEventFlow x) = some x) ∧
        (∀ x y : ContourSumWindowUp,
          contourSumWindowToEventFlow x = contourSumWindowToEventFlow y → x = y) ∧
          contourSumWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact contourSumWindowDecode_encode_bhist
  · constructor
    · exact contourSumWindow_round_trip
    · constructor
      · intro x y heq
        exact contourSumWindowToEventFlow_injective heq
      · rfl

end BEDC.Derived.ContourSumWindowUp
