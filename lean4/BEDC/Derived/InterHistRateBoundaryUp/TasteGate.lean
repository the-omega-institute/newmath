import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# InterHistRateBoundaryUp TasteGate carrier.
-/

namespace BEDC.Derived.InterHistRateBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InterHistRateBoundaryUp : Type where
  | mk :
      (observerBoundary causalRoute rateGate maximumRate observerSymmetry noGlobalFrame
        invariantReadback transport probeStability continuation provenance nameCert : BHist) →
      InterHistRateBoundaryUp
  deriving DecidableEq

def interHistRateBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: interHistRateBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: interHistRateBoundaryEncodeBHist h

def interHistRateBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (interHistRateBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (interHistRateBoundaryDecodeBHist tail)

private theorem interHistRateBoundaryDecodeEncodeBHist :
    ∀ h : BHist,
      interHistRateBoundaryDecodeBHist (interHistRateBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def interHistRateBoundaryFields :
    InterHistRateBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InterHistRateBoundaryUp.mk observerBoundary causalRoute rateGate maximumRate
      observerSymmetry noGlobalFrame invariantReadback transport probeStability continuation
      provenance nameCert =>
      [observerBoundary, causalRoute, rateGate, maximumRate, observerSymmetry, noGlobalFrame,
        invariantReadback, transport, probeStability, continuation, provenance, nameCert]

def interHistRateBoundaryToEventFlow :
    InterHistRateBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (interHistRateBoundaryFields x).map interHistRateBoundaryEncodeBHist

def interHistRateBoundaryFromEventFlow :
    EventFlow → Option InterHistRateBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | observerBoundary :: rest0 =>
      match rest0 with
      | [] => none
      | causalRoute :: rest1 =>
          match rest1 with
          | [] => none
          | rateGate :: rest2 =>
              match rest2 with
              | [] => none
              | maximumRate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | observerSymmetry :: rest4 =>
                      match rest4 with
                      | [] => none
                      | noGlobalFrame :: rest5 =>
                          match rest5 with
                          | [] => none
                          | invariantReadback :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | probeStability :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | continuation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | nameCert :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (InterHistRateBoundaryUp.mk
                                                          (interHistRateBoundaryDecodeBHist
                                                            observerBoundary)
                                                          (interHistRateBoundaryDecodeBHist
                                                            causalRoute)
                                                          (interHistRateBoundaryDecodeBHist
                                                            rateGate)
                                                          (interHistRateBoundaryDecodeBHist
                                                            maximumRate)
                                                          (interHistRateBoundaryDecodeBHist
                                                            observerSymmetry)
                                                          (interHistRateBoundaryDecodeBHist
                                                            noGlobalFrame)
                                                          (interHistRateBoundaryDecodeBHist
                                                            invariantReadback)
                                                          (interHistRateBoundaryDecodeBHist
                                                            transport)
                                                          (interHistRateBoundaryDecodeBHist
                                                            probeStability)
                                                          (interHistRateBoundaryDecodeBHist
                                                            continuation)
                                                          (interHistRateBoundaryDecodeBHist
                                                            provenance)
                                                          (interHistRateBoundaryDecodeBHist
                                                            nameCert))
                                                  | _ :: _ => none

private theorem interHistRateBoundaryRoundTrip :
    ∀ x : InterHistRateBoundaryUp,
      interHistRateBoundaryFromEventFlow
        (interHistRateBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerBoundary causalRoute rateGate maximumRate observerSymmetry noGlobalFrame
      invariantReadback transport probeStability continuation provenance nameCert =>
      change
        some
          (InterHistRateBoundaryUp.mk
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist observerBoundary))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist causalRoute))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist rateGate))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist maximumRate))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist observerSymmetry))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist noGlobalFrame))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist invariantReadback))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist transport))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist probeStability))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist continuation))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist provenance))
            (interHistRateBoundaryDecodeBHist
              (interHistRateBoundaryEncodeBHist nameCert))) =
          some
            (InterHistRateBoundaryUp.mk observerBoundary causalRoute rateGate maximumRate
              observerSymmetry noGlobalFrame invariantReadback transport probeStability
              continuation provenance nameCert)
      rw [interHistRateBoundaryDecodeEncodeBHist observerBoundary,
        interHistRateBoundaryDecodeEncodeBHist causalRoute,
        interHistRateBoundaryDecodeEncodeBHist rateGate,
        interHistRateBoundaryDecodeEncodeBHist maximumRate,
        interHistRateBoundaryDecodeEncodeBHist observerSymmetry,
        interHistRateBoundaryDecodeEncodeBHist noGlobalFrame,
        interHistRateBoundaryDecodeEncodeBHist invariantReadback,
        interHistRateBoundaryDecodeEncodeBHist transport,
        interHistRateBoundaryDecodeEncodeBHist probeStability,
        interHistRateBoundaryDecodeEncodeBHist continuation,
        interHistRateBoundaryDecodeEncodeBHist provenance,
        interHistRateBoundaryDecodeEncodeBHist nameCert]

private theorem interHistRateBoundaryToEventFlow_injective
    {x y : InterHistRateBoundaryUp} :
    interHistRateBoundaryToEventFlow x =
      interHistRateBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      interHistRateBoundaryFromEventFlow
          (interHistRateBoundaryToEventFlow x) =
        interHistRateBoundaryFromEventFlow
          (interHistRateBoundaryToEventFlow y) :=
    congrArg interHistRateBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (interHistRateBoundaryRoundTrip x).symm
      (Eq.trans hread (interHistRateBoundaryRoundTrip y)))

private theorem interHistRateBoundaryFieldsFaithful :
    ∀ x y : InterHistRateBoundaryUp,
      interHistRateBoundaryFields x = interHistRateBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observerBoundary₁ causalRoute₁ rateGate₁ maximumRate₁ observerSymmetry₁
      noGlobalFrame₁ invariantReadback₁ transport₁ probeStability₁ continuation₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk observerBoundary₂ causalRoute₂ rateGate₂ maximumRate₂ observerSymmetry₂
          noGlobalFrame₂ invariantReadback₂ transport₂ probeStability₂ continuation₂
          provenance₂ nameCert₂ =>
          injection hfields with hObserverBoundary tail0
          injection tail0 with hCausalRoute tail1
          injection tail1 with hRateGate tail2
          injection tail2 with hMaximumRate tail3
          injection tail3 with hObserverSymmetry tail4
          injection tail4 with hNoGlobalFrame tail5
          injection tail5 with hInvariantReadback tail6
          injection tail6 with hTransport tail7
          injection tail7 with hProbeStability tail8
          injection tail8 with hContinuation tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hNameCert _
          cases hObserverBoundary
          cases hCausalRoute
          cases hRateGate
          cases hMaximumRate
          cases hObserverSymmetry
          cases hNoGlobalFrame
          cases hInvariantReadback
          cases hTransport
          cases hProbeStability
          cases hContinuation
          cases hProvenance
          cases hNameCert
          rfl

instance interHistRateBoundaryBHistCarrier :
    BHistCarrier InterHistRateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := interHistRateBoundaryToEventFlow
  fromEventFlow := interHistRateBoundaryFromEventFlow

instance interHistRateBoundaryChapterTasteGate :
    ChapterTasteGate InterHistRateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change interHistRateBoundaryFromEventFlow
      (interHistRateBoundaryToEventFlow x) = some x
    exact interHistRateBoundaryRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (interHistRateBoundaryToEventFlow_injective heq)

instance interHistRateBoundaryFieldFaithful :
    FieldFaithful InterHistRateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := interHistRateBoundaryFields
  field_faithful := interHistRateBoundaryFieldsFaithful

instance interHistRateBoundaryNontrivial :
    Nontrivial InterHistRateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InterHistRateBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InterHistRateBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InterHistRateBoundaryUp :=
  interHistRateBoundaryChapterTasteGate

theorem InterHistRateBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate InterHistRateBoundaryUp) ∧
      Nonempty (FieldFaithful InterHistRateBoundaryUp) ∧
      Nonempty (Nontrivial InterHistRateBoundaryUp) ∧
        (∀ h : BHist,
          interHistRateBoundaryDecodeBHist
            (interHistRateBoundaryEncodeBHist h) = h) ∧
          interHistRateBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨interHistRateBoundaryChapterTasteGate⟩,
      ⟨interHistRateBoundaryFieldFaithful⟩,
      ⟨interHistRateBoundaryNontrivial⟩,
      interHistRateBoundaryDecodeEncodeBHist, rfl⟩

end BEDC.Derived.InterHistRateBoundaryUp
