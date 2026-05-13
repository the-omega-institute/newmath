import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverPerspectiveCompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverPerspectiveCompositionUp : Type where
  | mk :
      (classifierLeft classifierRight coupling alignment transport routes provenance nameCert :
        BHist) →
        ObserverPerspectiveCompositionUp
  deriving DecidableEq

def observerPerspectiveCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerPerspectiveCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerPerspectiveCompositionEncodeBHist h

def observerPerspectiveCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerPerspectiveCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerPerspectiveCompositionDecodeBHist tail)

private theorem observerPerspectiveCompositionDecodeEncodeBHist :
    ∀ h : BHist,
      observerPerspectiveCompositionDecodeBHist (observerPerspectiveCompositionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerPerspectiveCompositionToEventFlow :
    ObserverPerspectiveCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverPerspectiveCompositionUp.mk classifierLeft classifierRight coupling alignment
      transport routes provenance nameCert =>
      [[BMark.b0],
        observerPerspectiveCompositionEncodeBHist classifierLeft,
        [BMark.b1, BMark.b0],
        observerPerspectiveCompositionEncodeBHist classifierRight,
        [BMark.b1, BMark.b1, BMark.b0],
        observerPerspectiveCompositionEncodeBHist coupling,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerPerspectiveCompositionEncodeBHist alignment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerPerspectiveCompositionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerPerspectiveCompositionEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerPerspectiveCompositionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerPerspectiveCompositionEncodeBHist nameCert]

def observerPerspectiveCompositionFromEventFlow :
    EventFlow → Option ObserverPerspectiveCompositionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | classifierLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | classifierRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | coupling :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | alignment :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ObserverPerspectiveCompositionUp.mk
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            classifierLeft)
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            classifierRight)
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            coupling)
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            alignment)
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            transport)
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            routes)
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            provenance)
                                                                          (observerPerspectiveCompositionDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ =>
                                                                      none

private theorem observerPerspectiveCompositionRoundTrip :
    ∀ x : ObserverPerspectiveCompositionUp,
      observerPerspectiveCompositionFromEventFlow
        (observerPerspectiveCompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk classifierLeft classifierRight coupling alignment transport routes provenance nameCert =>
      change
        some
          (ObserverPerspectiveCompositionUp.mk
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist classifierLeft))
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist classifierRight))
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist coupling))
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist alignment))
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist transport))
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist routes))
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist provenance))
            (observerPerspectiveCompositionDecodeBHist
              (observerPerspectiveCompositionEncodeBHist nameCert))) =
          some
            (ObserverPerspectiveCompositionUp.mk classifierLeft classifierRight coupling
              alignment transport routes provenance nameCert)
      rw [observerPerspectiveCompositionDecodeEncodeBHist classifierLeft,
        observerPerspectiveCompositionDecodeEncodeBHist classifierRight,
        observerPerspectiveCompositionDecodeEncodeBHist coupling,
        observerPerspectiveCompositionDecodeEncodeBHist alignment,
        observerPerspectiveCompositionDecodeEncodeBHist transport,
        observerPerspectiveCompositionDecodeEncodeBHist routes,
        observerPerspectiveCompositionDecodeEncodeBHist provenance,
        observerPerspectiveCompositionDecodeEncodeBHist nameCert]

private theorem observerPerspectiveCompositionToEventFlow_injective
    {x y : ObserverPerspectiveCompositionUp} :
    observerPerspectiveCompositionToEventFlow x =
      observerPerspectiveCompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerPerspectiveCompositionFromEventFlow
          (observerPerspectiveCompositionToEventFlow x) =
        observerPerspectiveCompositionFromEventFlow
          (observerPerspectiveCompositionToEventFlow y) :=
    congrArg observerPerspectiveCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerPerspectiveCompositionRoundTrip x).symm
      (Eq.trans hread (observerPerspectiveCompositionRoundTrip y)))

instance observerPerspectiveCompositionBHistCarrier :
    BHistCarrier ObserverPerspectiveCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerPerspectiveCompositionToEventFlow
  fromEventFlow := observerPerspectiveCompositionFromEventFlow

instance observerPerspectiveCompositionChapterTasteGate :
    ChapterTasteGate ObserverPerspectiveCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerPerspectiveCompositionFromEventFlow
        (observerPerspectiveCompositionToEventFlow x) = some x
    exact observerPerspectiveCompositionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerPerspectiveCompositionToEventFlow_injective heq)

theorem ObserverPerspectiveCompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerPerspectiveCompositionDecodeBHist
        (observerPerspectiveCompositionEncodeBHist h) = h) ∧
      (∀ x : ObserverPerspectiveCompositionUp,
        observerPerspectiveCompositionFromEventFlow
          (observerPerspectiveCompositionToEventFlow x) = some x) ∧
        (∀ x y : ObserverPerspectiveCompositionUp,
          observerPerspectiveCompositionToEventFlow x =
            observerPerspectiveCompositionToEventFlow y → x = y) ∧
          observerPerspectiveCompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨observerPerspectiveCompositionDecodeEncodeBHist,
      observerPerspectiveCompositionRoundTrip,
      fun _x _y heq => observerPerspectiveCompositionToEventFlow_injective heq, rfl⟩

end BEDC.Derived.ObserverPerspectiveCompositionUp
