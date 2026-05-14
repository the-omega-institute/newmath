import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelMorphismUp : Type where
  | mk :
      (source target map markPreservation histPreservation extPreservation contPreservation
        sigPreservation packagePreservation provenance nameCert : BHist) →
      KernelMorphismUp
  deriving DecidableEq

private def kernelMorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelMorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelMorphismEncodeBHist h

private def kernelMorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelMorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelMorphismDecodeBHist tail)

private theorem kernelMorphismDecode_encode_bhist :
    ∀ h : BHist, kernelMorphismDecodeBHist (kernelMorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem kernelMorphism_mk_congr
    {source source' target target' map map' markPreservation markPreservation'
      histPreservation histPreservation' extPreservation extPreservation'
      contPreservation contPreservation' sigPreservation sigPreservation'
      packagePreservation packagePreservation' provenance provenance' nameCert nameCert' :
        BHist}
    (hSource : source' = source)
    (hTarget : target' = target)
    (hMap : map' = map)
    (hMarkPreservation : markPreservation' = markPreservation)
    (hHistPreservation : histPreservation' = histPreservation)
    (hExtPreservation : extPreservation' = extPreservation)
    (hContPreservation : contPreservation' = contPreservation)
    (hSigPreservation : sigPreservation' = sigPreservation)
    (hPackagePreservation : packagePreservation' = packagePreservation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    KernelMorphismUp.mk source' target' map' markPreservation' histPreservation'
        extPreservation' contPreservation' sigPreservation' packagePreservation'
        provenance' nameCert' =
      KernelMorphismUp.mk source target map markPreservation histPreservation extPreservation
        contPreservation sigPreservation packagePreservation provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hTarget
  cases hMap
  cases hMarkPreservation
  cases hHistPreservation
  cases hExtPreservation
  cases hContPreservation
  cases hSigPreservation
  cases hPackagePreservation
  cases hProvenance
  cases hNameCert
  rfl

private def kernelMorphismToEventFlow : KernelMorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelMorphismUp.mk source target map markPreservation histPreservation extPreservation
      contPreservation sigPreservation packagePreservation provenance nameCert =>
      [[BMark.b0],
        kernelMorphismEncodeBHist source,
        [BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist map,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist markPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist histPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist extPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist contPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelMorphismEncodeBHist sigPreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist packagePreservation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelMorphismEncodeBHist nameCert]

private def kernelMorphismFromEventFlow : EventFlow → Option KernelMorphismUp
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
                      | map :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | markPreservation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | histPreservation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | extPreservation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | contPreservation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | sigPreservation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | packagePreservation :: rest17 =>
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
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (KernelMorphismUp.mk
                                                                                                  (kernelMorphismDecodeBHist source)
                                                                                                  (kernelMorphismDecodeBHist target)
                                                                                                  (kernelMorphismDecodeBHist map)
                                                                                                  (kernelMorphismDecodeBHist markPreservation)
                                                                                                  (kernelMorphismDecodeBHist histPreservation)
                                                                                                  (kernelMorphismDecodeBHist extPreservation)
                                                                                                  (kernelMorphismDecodeBHist contPreservation)
                                                                                                  (kernelMorphismDecodeBHist sigPreservation)
                                                                                                  (kernelMorphismDecodeBHist packagePreservation)
                                                                                                  (kernelMorphismDecodeBHist provenance)
                                                                                                  (kernelMorphismDecodeBHist nameCert))
                                                                                          | _ :: _ => none

private theorem kernelMorphism_round_trip :
    ∀ x : KernelMorphismUp,
      kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target map markPreservation histPreservation extPreservation
      contPreservation sigPreservation packagePreservation provenance nameCert =>
      change
        some
          (KernelMorphismUp.mk
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist source))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist target))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist map))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist markPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist histPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist extPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist contPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist sigPreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist packagePreservation))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist provenance))
            (kernelMorphismDecodeBHist (kernelMorphismEncodeBHist nameCert))) =
          some
            (KernelMorphismUp.mk source target map markPreservation histPreservation
              extPreservation contPreservation sigPreservation packagePreservation provenance
              nameCert)
      exact
        congrArg some
          (kernelMorphism_mk_congr
            (kernelMorphismDecode_encode_bhist source)
            (kernelMorphismDecode_encode_bhist target)
            (kernelMorphismDecode_encode_bhist map)
            (kernelMorphismDecode_encode_bhist markPreservation)
            (kernelMorphismDecode_encode_bhist histPreservation)
            (kernelMorphismDecode_encode_bhist extPreservation)
            (kernelMorphismDecode_encode_bhist contPreservation)
            (kernelMorphismDecode_encode_bhist sigPreservation)
            (kernelMorphismDecode_encode_bhist packagePreservation)
            (kernelMorphismDecode_encode_bhist provenance)
            (kernelMorphismDecode_encode_bhist nameCert))

private theorem kernelMorphismToEventFlow_injective {x y : KernelMorphismUp} :
    kernelMorphismToEventFlow x = kernelMorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) =
        kernelMorphismFromEventFlow (kernelMorphismToEventFlow y) :=
    congrArg kernelMorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelMorphism_round_trip x).symm
      (Eq.trans hread (kernelMorphism_round_trip y)))

instance kernelMorphismBHistCarrier : BHistCarrier KernelMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelMorphismToEventFlow
  fromEventFlow := kernelMorphismFromEventFlow

instance kernelMorphismChapterTasteGate : ChapterTasteGate KernelMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) = some x
    exact kernelMorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelMorphismToEventFlow_injective heq)

theorem KernelMorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist, kernelMorphismDecodeBHist (kernelMorphismEncodeBHist h) = h) ∧
      (∀ x : KernelMorphismUp,
        kernelMorphismFromEventFlow (kernelMorphismToEventFlow x) = some x) ∧
        (∀ x y : KernelMorphismUp,
          kernelMorphismToEventFlow x = kernelMorphismToEventFlow y → x = y) ∧
          kernelMorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelMorphismDecode_encode_bhist
  · constructor
    · exact kernelMorphism_round_trip
    · constructor
      · intro x y heq
        exact kernelMorphismToEventFlow_injective heq
      · rfl

def KernelMorphismCarrier [AskSetup] [PackageSetup]
    (source target graph edgeAdmission classifierLift transport routes provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
    UnaryHistory edgeAdmission ∧ UnaryHistory classifierLift ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont source graph edgeAdmission ∧ Cont edgeAdmission classifierLift target ∧
          Cont transport routes provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle cert pkg

theorem KernelMorphismCarrier_source_target_scope [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert sourceRead
      targetRead graphRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg ->
      hsame sourceRead source ->
        hsame targetRead target ->
          hsame graphRead graph ->
            UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧ UnaryHistory graphRead ∧
              UnaryHistory edgeAdmission ∧ UnaryHistory classifierLift ∧
                Cont source graph edgeAdmission ∧ Cont edgeAdmission classifierLift target ∧
                  PkgSig bundle cert pkg := by
  intro carrier sourceSame targetSame graphSame
  obtain ⟨sourceUnary, targetUnary, graphUnary, edgeAdmissionUnary, classifierLiftUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _certUnary, sourceGraphAdmission,
    admissionClassifierTarget, _transportRoutesProvenance, _provenancePkg, certPkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport_symm sourceUnary sourceSame
  have targetReadUnary : UnaryHistory targetRead :=
    unary_transport_symm targetUnary targetSame
  have graphReadUnary : UnaryHistory graphRead :=
    unary_transport_symm graphUnary graphSame
  exact ⟨sourceReadUnary, targetReadUnary, graphReadUnary, edgeAdmissionUnary,
    classifierLiftUnary, sourceGraphAdmission, admissionClassifierTarget, certPkg⟩

theorem KernelMorphismCarrier_transport_stability_obligation [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert sourceP
      graphP classifierLiftP edgeAdmissionP targetP : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg →
      hsame source sourceP →
        hsame graph graphP →
          hsame classifierLift classifierLiftP →
            Cont sourceP graphP edgeAdmissionP →
              Cont edgeAdmissionP classifierLiftP targetP →
                KernelMorphismCarrier sourceP targetP graphP edgeAdmissionP classifierLiftP
                    transport routes provenance cert bundle pkg ∧
                  hsame edgeAdmission edgeAdmissionP ∧ hsame target targetP := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier sameSource sameGraph sameClassifierLift sourceGraphEdgeP edgeClassifierTargetP
  obtain ⟨sourceUnary, _targetUnary, graphUnary, edgeAdmissionUnary, classifierLiftUnary,
    transportUnary, routesUnary, provenanceUnary, certUnary, sourceGraphEdge,
    edgeClassifierTarget, transportRoutesProvenance, provenancePkg, certPkg⟩ := carrier
  have sourceUnaryP : UnaryHistory sourceP := unary_transport sourceUnary sameSource
  have graphUnaryP : UnaryHistory graphP := unary_transport graphUnary sameGraph
  have classifierLiftUnaryP : UnaryHistory classifierLiftP :=
    unary_transport classifierLiftUnary sameClassifierLift
  have edgeSame : hsame edgeAdmission edgeAdmissionP :=
    cont_respects_hsame sameSource sameGraph sourceGraphEdge sourceGraphEdgeP
  have edgeUnaryP : UnaryHistory edgeAdmissionP :=
    unary_cont_closed sourceUnaryP graphUnaryP sourceGraphEdgeP
  have targetSame : hsame target targetP :=
    cont_respects_hsame edgeSame sameClassifierLift edgeClassifierTarget edgeClassifierTargetP
  have targetUnaryP : UnaryHistory targetP :=
    unary_cont_closed edgeUnaryP classifierLiftUnaryP edgeClassifierTargetP
  exact
    ⟨⟨sourceUnaryP, targetUnaryP, graphUnaryP, edgeUnaryP, classifierLiftUnaryP,
        transportUnary, routesUnary, provenanceUnary, certUnary, sourceGraphEdgeP,
        edgeClassifierTargetP, transportRoutesProvenance, provenancePkg, certPkg⟩,
      edgeSame, targetSame⟩

def KernelMorphismEdgeLiftCarrier [AskSetup] [PackageSetup]
    (source target graph edgeAdmission classifierLift transport route provenance cert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
    UnaryHistory edgeAdmission ∧ UnaryHistory classifierLift ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        UnaryHistory endpoint ∧ Cont source edgeAdmission target ∧
          Cont target classifierLift graph ∧ Cont graph route endpoint ∧
            PkgSig bundle endpoint pkg

theorem KernelMorphismCarrier_edge_lift_transport [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport route provenance cert endpoint
      source' edgeAdmission' classifierLift' target' graph' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismEdgeLiftCarrier source target graph edgeAdmission classifierLift transport route
        provenance cert endpoint bundle pkg →
      hsame source source' →
        hsame edgeAdmission edgeAdmission' →
          hsame classifierLift classifierLift' →
            Cont source' edgeAdmission' target' →
              Cont target' classifierLift' graph' →
                Cont graph' route endpoint' →
                  PkgSig bundle endpoint' pkg →
                    KernelMorphismEdgeLiftCarrier source' target' graph' edgeAdmission'
                        classifierLift' transport route provenance cert endpoint' bundle pkg ∧
                      hsame target target' ∧ hsame graph graph' ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sameSource sameAdmission sameLift sourceAdmission' targetLift' graphEndpoint'
    endpointPkg'
  obtain ⟨sourceUnary, targetUnary, graphUnary, admissionUnary, liftUnary, transportUnary,
    routeUnary, provenanceUnary, certUnary, endpointUnary, sourceAdmission, targetLift,
    graphEndpoint, endpointPkg⟩ := carrier
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have admissionUnary' : UnaryHistory edgeAdmission' :=
    unary_transport admissionUnary sameAdmission
  have liftUnary' : UnaryHistory classifierLift' := unary_transport liftUnary sameLift
  have targetSame : hsame target target' :=
    cont_respects_hsame sameSource sameAdmission sourceAdmission sourceAdmission'
  have targetUnary' : UnaryHistory target' :=
    unary_cont_closed sourceUnary' admissionUnary' sourceAdmission'
  have graphSame : hsame graph graph' :=
    cont_respects_hsame targetSame sameLift targetLift targetLift'
  have graphUnary' : UnaryHistory graph' :=
    unary_cont_closed targetUnary' liftUnary' targetLift'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame graphSame (hsame_refl route) graphEndpoint graphEndpoint'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed graphUnary' routeUnary graphEndpoint'
  exact
    ⟨⟨sourceUnary', targetUnary', graphUnary', admissionUnary', liftUnary', transportUnary,
        routeUnary, provenanceUnary, certUnary, endpointUnary', sourceAdmission', targetLift',
        graphEndpoint', endpointPkg'⟩,
      targetSame, graphSame, endpointSame⟩

theorem KernelMorphismCarrier_scoped_edge_lift_consumer [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport route provenance cert endpoint
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismEdgeLiftCarrier source target graph edgeAdmission classifierLift transport route
        provenance cert endpoint bundle pkg →
      hsame endpointRead endpoint →
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
          UnaryHistory endpointRead ∧ Cont source edgeAdmission target ∧
            Cont target classifierLift graph ∧ Cont graph route endpoint ∧
              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier endpointSame
  obtain ⟨sourceUnary, targetUnary, graphUnary, _admissionUnary, _liftUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _certUnary, endpointUnary, sourceAdmissionTarget,
    targetLiftGraph, graphRouteEndpoint, endpointPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_transport_symm endpointUnary endpointSame
  exact
    ⟨sourceUnary, targetUnary, graphUnary, endpointReadUnary, sourceAdmissionTarget,
      targetLiftGraph, graphRouteEndpoint, endpointPkg⟩

theorem KernelMorphismCarrier_composition_scope [AskSetup] [PackageSetup]
    {source middle target graphLeft graphRight edgeLeft edgeRight liftLeft liftRight
      transportLeft routesLeft provenanceLeft certLeft transportRight routesRight provenanceRight
      certRight compositeGraph compositeEdge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source middle graphLeft edgeLeft liftLeft transportLeft routesLeft
        provenanceLeft certLeft bundle pkg →
      KernelMorphismCarrier middle target graphRight edgeRight liftRight transportRight
          routesRight provenanceRight certRight bundle pkg →
        Cont graphLeft graphRight compositeGraph →
          Cont edgeLeft edgeRight compositeEdge →
            PkgSig bundle compositeEdge pkg →
              UnaryHistory source ∧ UnaryHistory middle ∧ UnaryHistory target ∧
                UnaryHistory graphLeft ∧ UnaryHistory graphRight ∧ UnaryHistory compositeGraph ∧
                  UnaryHistory compositeEdge ∧ Cont graphLeft graphRight compositeGraph ∧
                    Cont edgeLeft edgeRight compositeEdge ∧ PkgSig bundle compositeEdge pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro leftCarrier rightCarrier graphComposition edgeComposition compositePkg
  obtain ⟨sourceUnary, middleUnary, graphLeftUnary, edgeLeftUnary, _liftLeftUnary,
    _transportLeftUnary, _routesLeftUnary, _provenanceLeftUnary, _certLeftUnary,
    _sourceGraphLeftEdge, _edgeLiftLeftMiddle, _transportLeftRoutesProvenance,
    _provenanceLeftPkg, _certLeftPkg⟩ := leftCarrier
  obtain ⟨_middleUnaryRight, targetUnary, graphRightUnary, edgeRightUnary, _liftRightUnary,
    _transportRightUnary, _routesRightUnary, _provenanceRightUnary, _certRightUnary,
    _middleGraphRightEdge, _edgeLiftRightTarget, _transportRightRoutesProvenance,
    _provenanceRightPkg, _certRightPkg⟩ := rightCarrier
  have compositeGraphUnary : UnaryHistory compositeGraph :=
    unary_cont_closed graphLeftUnary graphRightUnary graphComposition
  have compositeEdgeUnary : UnaryHistory compositeEdge :=
    unary_cont_closed edgeLeftUnary edgeRightUnary edgeComposition
  exact
    ⟨sourceUnary, middleUnary, targetUnary, graphLeftUnary, graphRightUnary,
      compositeGraphUnary, compositeEdgeUnary, graphComposition, edgeComposition, compositePkg⟩

theorem KernelMorphismCarrier_classifier_lift_obligation [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert
      sourceRead graphRead edgeRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg →
      hsame sourceRead source →
        hsame graphRead graph →
          hsame edgeRead edgeAdmission →
            hsame targetRead target →
              UnaryHistory sourceRead ∧ UnaryHistory graphRead ∧ UnaryHistory edgeRead ∧
                UnaryHistory targetRead ∧ Cont edgeAdmission classifierLift target ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier sourceSame graphSame edgeSame targetSame
  obtain ⟨sourceUnary, targetUnary, graphUnary, edgeUnary, _liftUnary, _transportUnary,
    _routesUnary, _provenanceUnary, _certUnary, _sourceGraphEdge, edgeLiftTarget,
    _transportRoutesProvenance, provenancePkg, certPkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport_symm sourceUnary sourceSame
  have graphReadUnary : UnaryHistory graphRead :=
    unary_transport_symm graphUnary graphSame
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_transport_symm edgeUnary edgeSame
  have targetReadUnary : UnaryHistory targetRead :=
    unary_transport_symm targetUnary targetSame
  exact
    ⟨sourceReadUnary, graphReadUnary, edgeReadUnary, targetReadUnary, edgeLiftTarget,
      provenancePkg, certPkg⟩

theorem KernelMorphismCarrier_namecert_scope [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert
      sourceRead targetRead graphRead edgeRead liftRead transportRead routesRead provenanceRead
      certRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg →
      hsame sourceRead source →
        hsame targetRead target →
          hsame graphRead graph →
            hsame edgeRead edgeAdmission →
              hsame liftRead classifierLift →
                hsame transportRead transport →
                  hsame routesRead routes →
                    hsame provenanceRead provenance →
                      hsame certRead cert →
                        UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                          UnaryHistory graphRead ∧ UnaryHistory edgeRead ∧
                            UnaryHistory liftRead ∧ UnaryHistory transportRead ∧
                              UnaryHistory routesRead ∧ UnaryHistory provenanceRead ∧
                                UnaryHistory certRead ∧ Cont source graph edgeAdmission ∧
                                  Cont edgeAdmission classifierLift target ∧
                                    Cont transport routes provenance ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier sourceSame targetSame graphSame edgeSame liftSame transportSame routesSame
    provenanceSame certSame
  obtain ⟨sourceUnary, targetUnary, graphUnary, edgeUnary, liftUnary, transportUnary,
    routesUnary, provenanceUnary, certUnary, sourceGraphEdge, edgeLiftTarget,
    transportRoutesProvenance, provenancePkg, certPkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport_symm sourceUnary sourceSame
  have targetReadUnary : UnaryHistory targetRead :=
    unary_transport_symm targetUnary targetSame
  have graphReadUnary : UnaryHistory graphRead :=
    unary_transport_symm graphUnary graphSame
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_transport_symm edgeUnary edgeSame
  have liftReadUnary : UnaryHistory liftRead :=
    unary_transport_symm liftUnary liftSame
  have transportReadUnary : UnaryHistory transportRead :=
    unary_transport_symm transportUnary transportSame
  have routesReadUnary : UnaryHistory routesRead :=
    unary_transport_symm routesUnary routesSame
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_transport_symm provenanceUnary provenanceSame
  have certReadUnary : UnaryHistory certRead :=
    unary_transport_symm certUnary certSame
  exact
    ⟨sourceReadUnary, targetReadUnary, graphReadUnary, edgeReadUnary, liftReadUnary,
      transportReadUnary, routesReadUnary, provenanceReadUnary, certReadUnary,
      sourceGraphEdge, edgeLiftTarget, transportRoutesProvenance, provenancePkg, certPkg⟩

end BEDC.Derived.KernelMorphismUp
