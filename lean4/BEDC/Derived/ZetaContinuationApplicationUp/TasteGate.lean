import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZetaContinuationApplicationUp : Type where
  | mk :
      (eta functional pole zero gamma application transport continuation provenance name :
        BHist) →
      ZetaContinuationApplicationUp
  deriving DecidableEq

private def zetaContinuationApplicationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zetaContinuationApplicationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zetaContinuationApplicationEncodeBHist h

private def zetaContinuationApplicationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zetaContinuationApplicationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zetaContinuationApplicationDecodeBHist tail)

private theorem zetaContinuationApplicationDecode_encode_bhist :
    ∀ h : BHist,
      zetaContinuationApplicationDecodeBHist
        (zetaContinuationApplicationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem zetaContinuationApplication_mk_congr
    {eta eta' functional functional' pole pole' zero zero' gamma gamma'
      application application' transport transport' continuation continuation'
      provenance provenance' name name' : BHist}
    (hEta : eta' = eta)
    (hFunctional : functional' = functional)
    (hPole : pole' = pole)
    (hZero : zero' = zero)
    (hGamma : gamma' = gamma)
    (hApplication : application' = application)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ZetaContinuationApplicationUp.mk eta' functional' pole' zero' gamma' application'
        transport' continuation' provenance' name' =
      ZetaContinuationApplicationUp.mk eta functional pole zero gamma application transport
        continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEta
  cases hFunctional
  cases hPole
  cases hZero
  cases hGamma
  cases hApplication
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

private def zetaContinuationApplicationToEventFlow :
    ZetaContinuationApplicationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ZetaContinuationApplicationUp.mk eta functional pole zero gamma application transport
      continuation provenance name =>
      [[BMark.b0],
        zetaContinuationApplicationEncodeBHist eta,
        [BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist functional,
        [BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist pole,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist zero,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist gamma,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist application,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        zetaContinuationApplicationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zetaContinuationApplicationEncodeBHist name]

private def zetaContinuationApplicationFromEventFlow :
    EventFlow → Option ZetaContinuationApplicationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | eta :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | functional :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | pole :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | zero :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gamma :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | application :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ZetaContinuationApplicationUp.mk
                                                                                          (zetaContinuationApplicationDecodeBHist eta)
                                                                                          (zetaContinuationApplicationDecodeBHist functional)
                                                                                          (zetaContinuationApplicationDecodeBHist pole)
                                                                                          (zetaContinuationApplicationDecodeBHist zero)
                                                                                          (zetaContinuationApplicationDecodeBHist gamma)
                                                                                          (zetaContinuationApplicationDecodeBHist application)
                                                                                          (zetaContinuationApplicationDecodeBHist transport)
                                                                                          (zetaContinuationApplicationDecodeBHist continuation)
                                                                                          (zetaContinuationApplicationDecodeBHist provenance)
                                                                                          (zetaContinuationApplicationDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem zetaContinuationApplication_round_trip :
    ∀ x : ZetaContinuationApplicationUp,
      zetaContinuationApplicationFromEventFlow
        (zetaContinuationApplicationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk eta functional pole zero gamma application transport continuation provenance name =>
      change
        some
          (ZetaContinuationApplicationUp.mk
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist eta))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist functional))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist pole))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist zero))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist gamma))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist application))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist transport))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist continuation))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist provenance))
            (zetaContinuationApplicationDecodeBHist
              (zetaContinuationApplicationEncodeBHist name))) =
          some
            (ZetaContinuationApplicationUp.mk eta functional pole zero gamma application
              transport continuation provenance name)
      exact
        congrArg some
          (zetaContinuationApplication_mk_congr
            (zetaContinuationApplicationDecode_encode_bhist eta)
            (zetaContinuationApplicationDecode_encode_bhist functional)
            (zetaContinuationApplicationDecode_encode_bhist pole)
            (zetaContinuationApplicationDecode_encode_bhist zero)
            (zetaContinuationApplicationDecode_encode_bhist gamma)
            (zetaContinuationApplicationDecode_encode_bhist application)
            (zetaContinuationApplicationDecode_encode_bhist transport)
            (zetaContinuationApplicationDecode_encode_bhist continuation)
            (zetaContinuationApplicationDecode_encode_bhist provenance)
            (zetaContinuationApplicationDecode_encode_bhist name))

private theorem zetaContinuationApplicationToEventFlow_injective
    {x y : ZetaContinuationApplicationUp} :
    zetaContinuationApplicationToEventFlow x =
        zetaContinuationApplicationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zetaContinuationApplicationFromEventFlow (zetaContinuationApplicationToEventFlow x) =
        zetaContinuationApplicationFromEventFlow
          (zetaContinuationApplicationToEventFlow y) :=
    congrArg zetaContinuationApplicationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zetaContinuationApplication_round_trip x).symm
      (Eq.trans hread (zetaContinuationApplication_round_trip y)))

instance zetaContinuationApplicationBHistCarrier :
    BHistCarrier ZetaContinuationApplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zetaContinuationApplicationToEventFlow
  fromEventFlow := zetaContinuationApplicationFromEventFlow

instance zetaContinuationApplicationChapterTasteGate :
    ChapterTasteGate ZetaContinuationApplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      zetaContinuationApplicationFromEventFlow
        (zetaContinuationApplicationToEventFlow x) = some x
    exact zetaContinuationApplication_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zetaContinuationApplicationToEventFlow_injective heq)

theorem ZetaContinuationApplicationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      zetaContinuationApplicationDecodeBHist
        (zetaContinuationApplicationEncodeBHist h) = h) ∧
      (∀ x : ZetaContinuationApplicationUp,
        zetaContinuationApplicationFromEventFlow
          (zetaContinuationApplicationToEventFlow x) = some x) ∧
        (∀ x y : ZetaContinuationApplicationUp,
          zetaContinuationApplicationToEventFlow x =
              zetaContinuationApplicationToEventFlow y →
            x = y) ∧
          zetaContinuationApplicationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact zetaContinuationApplicationDecode_encode_bhist
  · constructor
    · exact zetaContinuationApplication_round_trip
    · constructor
      · intro x y heq
        exact zetaContinuationApplicationToEventFlow_injective heq
      · rfl

end BEDC.Derived.ZetaContinuationApplicationUp
