import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalBallCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalBallCompletionUp : Type where
  | mk :
      (metricSource formalBallFamily roundedIdeal dyadicRadius streamWindow realSeal
        transports replay provenance localName : BHist) →
        FormalBallCompletionUp
  deriving DecidableEq

def formalBallCompletionTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b0]

def formalBallCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalBallCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalBallCompletionEncodeBHist h

def formalBallCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalBallCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalBallCompletionDecodeBHist tail)

private theorem FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def formalBallCompletionFields : FormalBallCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FormalBallCompletionUp.mk metricSource formalBallFamily roundedIdeal dyadicRadius
      streamWindow realSeal transports replay provenance localName =>
      [metricSource, formalBallFamily, roundedIdeal, dyadicRadius, streamWindow, realSeal,
        transports, replay, provenance, localName]

def formalBallCompletionToEventFlow : FormalBallCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FormalBallCompletionUp.mk metricSource formalBallFamily roundedIdeal dyadicRadius
      streamWindow realSeal transports replay provenance localName =>
      [formalBallCompletionTag, formalBallCompletionEncodeBHist metricSource,
        formalBallCompletionEncodeBHist formalBallFamily,
        formalBallCompletionEncodeBHist roundedIdeal,
        formalBallCompletionEncodeBHist dyadicRadius,
        formalBallCompletionEncodeBHist streamWindow,
        formalBallCompletionEncodeBHist realSeal,
        formalBallCompletionEncodeBHist transports,
        formalBallCompletionEncodeBHist replay,
        formalBallCompletionEncodeBHist provenance,
        formalBallCompletionEncodeBHist localName]

def formalBallCompletionFromEventFlow : EventFlow → Option FormalBallCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | metricSource :: rest1 =>
          match rest1 with
          | formalBallFamily :: rest2 =>
              match rest2 with
              | roundedIdeal :: rest3 =>
                  match rest3 with
                  | dyadicRadius :: rest4 =>
                      match rest4 with
                      | streamWindow :: rest5 =>
                          match rest5 with
                          | realSeal :: rest6 =>
                              match rest6 with
                              | transports :: rest7 =>
                                  match rest7 with
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (FormalBallCompletionUp.mk
                                                      (formalBallCompletionDecodeBHist
                                                        metricSource)
                                                      (formalBallCompletionDecodeBHist
                                                        formalBallFamily)
                                                      (formalBallCompletionDecodeBHist
                                                        roundedIdeal)
                                                      (formalBallCompletionDecodeBHist
                                                        dyadicRadius)
                                                      (formalBallCompletionDecodeBHist
                                                        streamWindow)
                                                      (formalBallCompletionDecodeBHist realSeal)
                                                      (formalBallCompletionDecodeBHist
                                                        transports)
                                                      (formalBallCompletionDecodeBHist replay)
                                                      (formalBallCompletionDecodeBHist
                                                        provenance)
                                                      (formalBallCompletionDecodeBHist localName))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none

private theorem FormalBallCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FormalBallCompletionUp,
      formalBallCompletionFromEventFlow (formalBallCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricSource formalBallFamily roundedIdeal dyadicRadius streamWindow realSeal
      transports replay provenance localName =>
      change
        some
          (FormalBallCompletionUp.mk
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist metricSource))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist formalBallFamily))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist roundedIdeal))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist dyadicRadius))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist streamWindow))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist realSeal))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist transports))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist replay))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist provenance))
            (formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist localName))) =
          some
            (FormalBallCompletionUp.mk metricSource formalBallFamily roundedIdeal dyadicRadius
              streamWindow realSeal transports replay provenance localName)
      rw [FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode metricSource,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode formalBallFamily,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode roundedIdeal,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode dyadicRadius,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode streamWindow,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode realSeal,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode transports,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode replay,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode provenance,
        FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode localName]

private theorem FormalBallCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FormalBallCompletionUp} :
    formalBallCompletionToEventFlow x = formalBallCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalBallCompletionFromEventFlow (formalBallCompletionToEventFlow x) =
        formalBallCompletionFromEventFlow (formalBallCompletionToEventFlow y) :=
    congrArg formalBallCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FormalBallCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FormalBallCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem FormalBallCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FormalBallCompletionUp,
      formalBallCompletionFields x = formalBallCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricSource₁ formalBallFamily₁ roundedIdeal₁ dyadicRadius₁ streamWindow₁ realSeal₁
      transports₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk metricSource₂ formalBallFamily₂ roundedIdeal₂ dyadicRadius₂ streamWindow₂
          realSeal₂ transports₂ replay₂ provenance₂ localName₂ =>
          injection hfields with hMetricSource tail0
          injection tail0 with hFormalBallFamily tail1
          injection tail1 with hRoundedIdeal tail2
          injection tail2 with hDyadicRadius tail3
          injection tail3 with hStreamWindow tail4
          injection tail4 with hRealSeal tail5
          injection tail5 with hTransports tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hLocalName _
          subst hMetricSource
          subst hFormalBallFamily
          subst hRoundedIdeal
          subst hDyadicRadius
          subst hStreamWindow
          subst hRealSeal
          subst hTransports
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance formalBallCompletionBHistCarrier : BHistCarrier FormalBallCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalBallCompletionToEventFlow
  fromEventFlow := formalBallCompletionFromEventFlow

instance formalBallCompletionChapterTasteGate :
    ChapterTasteGate FormalBallCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change formalBallCompletionFromEventFlow (formalBallCompletionToEventFlow x) = some x
    exact FormalBallCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FormalBallCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance formalBallCompletionFieldFaithful : FieldFaithful FormalBallCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := formalBallCompletionFields
  field_faithful := FormalBallCompletionTasteGate_single_carrier_alignment_fields_faithful

theorem FormalBallCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FormalBallCompletionUp) ∧
      Nonempty (ChapterTasteGate FormalBallCompletionUp) ∧
        Nonempty (FieldFaithful FormalBallCompletionUp) ∧
          (∀ h : BHist,
            formalBallCompletionDecodeBHist (formalBallCompletionEncodeBHist h) = h) ∧
            (∀ x : FormalBallCompletionUp,
              formalBallCompletionFromEventFlow (formalBallCompletionToEventFlow x) = some x) ∧
              formalBallCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro formalBallCompletionBHistCarrier
  · constructor
    · exact Nonempty.intro formalBallCompletionChapterTasteGate
    · constructor
      · exact Nonempty.intro formalBallCompletionFieldFaithful
      · constructor
        · exact FormalBallCompletionTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact FormalBallCompletionTasteGate_single_carrier_alignment_round_trip
          · rfl

end BEDC.Derived.FormalBallCompletionUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FormalBallCarrier [AskSetup] [PackageSetup]
    (metric radius dyadic window transport replay provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory metric ∧ UnaryHistory radius ∧ UnaryHistory dyadic ∧
    UnaryHistory window ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont metric radius dyadic ∧
        Cont dyadic window replay ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg

theorem FormalBallCarrier_completion_dependency_scope [AskSetup] [PackageSetup]
    {metric radius dyadic window transport replay provenance nameCert completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier metric radius dyadic window transport replay provenance nameCert bundle
        pkg ->
      Cont metric radius dyadic ->
        Cont dyadic window completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory metric ∧ UnaryHistory radius ∧ UnaryHistory dyadic ∧
              UnaryHistory window ∧ UnaryHistory completionRead ∧ Cont metric radius dyadic ∧
                Cont dyadic window completionRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier metricRadiusDyadic dyadicWindowCompletion completionPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowCompletion
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, completionUnary,
      metricRadiusDyadic, dyadicWindowCompletion, provenancePkg, completionPkg⟩

theorem FormalBallCarrier_radius_refinement [AskSetup] [PackageSetup]
    {metric radius dyadic window transport replay provenance nameCert refinedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier metric radius dyadic window transport replay provenance nameCert bundle
        pkg ->
      Cont radius dyadic refinedWindow ->
        PkgSig bundle refinedWindow pkg ->
          UnaryHistory metric ∧ UnaryHistory radius ∧ UnaryHistory dyadic ∧
            UnaryHistory refinedWindow ∧ Cont radius dyadic refinedWindow ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle refinedWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusDyadicRefined refinedPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, _windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed radiusUnary dyadicUnary radiusDyadicRefined
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, refinedUnary, radiusDyadicRefined,
      provenancePkg, refinedPkg⟩

end BEDC.Derived.FormalBallUp
