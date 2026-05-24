import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionUnitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionUnitCarrier [AskSetup] [PackageSetup]
    (source window tolerance readback sealRow completion transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory tolerance ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory completion ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont source window tolerance ∧ Cont tolerance readback sealRow ∧
          Cont sealRow route completion ∧ hsame transport BHist.Empty ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

def CauchyCompletionUnitClassifier [AskSetup] [PackageSetup]
    (source window tolerance readback sealRow completion transport route provenance name source'
      window' tolerance' readback' sealRow' completion' transport' route' provenance' name' :
        BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport
      route provenance name bundle pkg ∧
    CauchyCompletionUnitCarrier source' window' tolerance' readback' sealRow' completion'
        transport' route' provenance' name' bundle pkg ∧
      hsame source source' ∧ hsame window window' ∧ hsame tolerance tolerance' ∧
        hsame readback readback' ∧ hsame sealRow sealRow' ∧ hsame completion completion' ∧
          hsame transport transport' ∧ hsame route route' ∧
            Cont source window tolerance ∧ Cont tolerance readback sealRow ∧
              Cont sealRow route completion ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle provenance' pkg

theorem CauchyCompletionUnitCarrier_dense_embedding_handoff [AskSetup] [PackageSetup]
    {source window tolerance readback sealRow completion transport route provenance name
      denseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport route
        provenance name bundle pkg ->
      Cont completion route denseRead ->
        PkgSig bundle denseRead pkg ->
          UnaryHistory source ∧ UnaryHistory completion ∧ UnaryHistory denseRead ∧
            Cont source window tolerance ∧ Cont tolerance readback sealRow ∧
              Cont sealRow route completion ∧ Cont completion route denseRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle denseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier denseRoute densePkg
  obtain ⟨sourceUnary, _windowUnary, _toleranceUnary, _readbackUnary, _sealUnary,
    completionUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
      sourceWindowRoute, toleranceReadbackRoute, sealCompletionRoute, _transportEmpty,
        provenancePkg, _namePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary routeUnary denseRoute
  exact
    ⟨sourceUnary, completionUnary, denseUnary, sourceWindowRoute, toleranceReadbackRoute,
      sealCompletionRoute, denseRoute, provenancePkg, densePkg⟩

theorem CauchyCompletionUnitNameCert_obligations [AskSetup] [PackageSetup]
    {source window tolerance readback sealRow completion transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport
            route provenance name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport
            route provenance name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport
            route provenance name bundle pkg ∧ hsame row completion)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro completion ⟨carrier, hsame_refl completion⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchyCompletionUnitCarrier_constant_window_induction [AskSetup] [PackageSetup]
    {source window tolerance readback sealRow completion transport route provenance name
      request : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport route
        provenance name bundle pkg ->
      UnaryHistory request ->
        exists generatedWindow generatedTolerance : BHist,
          Cont source request generatedWindow ∧ Cont generatedWindow tolerance generatedTolerance ∧
            UnaryHistory generatedWindow ∧ UnaryHistory generatedTolerance ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier requestUnary
  obtain ⟨sourceUnary, _windowUnary, toleranceUnary, _readbackUnary, _sealUnary,
    _completionUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
      _sourceWindowRoute, _toleranceReadbackRoute, _sealCompletionRoute, _transportEmpty,
        provenancePkg, _namePkg⟩ := carrier
  let generatedWindow : BHist := BEDC.FKernel.Cont.append source request
  let generatedTolerance : BHist := BEDC.FKernel.Cont.append generatedWindow tolerance
  have windowCont : Cont source request generatedWindow := rfl
  have generatedWindowUnary : UnaryHistory generatedWindow :=
    unary_cont_closed sourceUnary requestUnary windowCont
  have toleranceCont : Cont generatedWindow tolerance generatedTolerance := rfl
  have generatedToleranceUnary : UnaryHistory generatedTolerance :=
    unary_cont_closed generatedWindowUnary toleranceUnary toleranceCont
  exact
    ⟨generatedWindow, generatedTolerance, windowCont, toleranceCont, generatedWindowUnary,
      generatedToleranceUnary, provenancePkg⟩

theorem CauchyCompletionUnitCarrier_real_completion_consumer_boundary [AskSetup] [PackageSetup]
    {source window tolerance readback sealRow completion transport route provenance name
      realConsumer completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport route
        provenance name bundle pkg ->
      Cont sealRow route realConsumer ->
        Cont completion route completionConsumer ->
          PkgSig bundle realConsumer pkg ->
            PkgSig bundle completionConsumer pkg ->
              UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory tolerance ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory completion ∧
                  UnaryHistory realConsumer ∧ UnaryHistory completionConsumer ∧
                    Cont source window tolerance ∧ Cont tolerance readback sealRow ∧
                      Cont sealRow route realConsumer ∧ Cont completion route completionConsumer ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realConsumer pkg ∧
                          PkgSig bundle completionConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier realConsumerCont completionConsumerCont realConsumerPkg completionConsumerPkg
  obtain ⟨sourceUnary, windowUnary, toleranceUnary, readbackUnary, sealUnary,
    completionUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
      sourceWindowRoute, toleranceReadbackRoute, _sealCompletionRoute, _transportEmpty,
        provenancePkg, _namePkg⟩ := carrier
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed sealUnary routeUnary realConsumerCont
  have completionConsumerUnary : UnaryHistory completionConsumer :=
    unary_cont_closed completionUnary routeUnary completionConsumerCont
  exact
    ⟨sourceUnary, windowUnary, toleranceUnary, readbackUnary, sealUnary, completionUnary,
      realConsumerUnary, completionConsumerUnary, sourceWindowRoute, toleranceReadbackRoute,
      realConsumerCont, completionConsumerCont, provenancePkg, realConsumerPkg,
      completionConsumerPkg⟩

theorem CauchyCompletionUnitCarrier_classifier_stability [AskSetup] [PackageSetup]
    {source source' window window' tolerance tolerance' readback readback' sealRow sealRow'
      completion completion' transport transport' route route' provenance provenance' name name' :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport route
        provenance name bundle pkg ->
      hsame source source' ->
        hsame window window' ->
          hsame tolerance tolerance' ->
            hsame readback readback' ->
              hsame sealRow sealRow' ->
                hsame completion completion' ->
                  hsame transport transport' ->
                    hsame route route' ->
                      hsame provenance provenance' ->
                        hsame name name' ->
                          Cont source' window' tolerance' ->
                            Cont tolerance' readback' sealRow' ->
                              Cont sealRow' route' completion' ->
                                PkgSig bundle provenance' pkg ->
                                  PkgSig bundle name' pkg ->
                                    CauchyCompletionUnitCarrier source' window' tolerance'
                                      readback' sealRow' completion' transport' route'
                                      provenance' name' bundle pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro carrier sameSource sameWindow sameTolerance sameReadback sameSeal sameCompletion
    sameTransport sameRoute sameProvenance sameName sourceWindow' toleranceReadback'
      sealCompletion' provenancePkg' namePkg'
  obtain ⟨sourceUnary, windowUnary, toleranceUnary, readbackUnary, sealUnary,
    completionUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
      _sourceWindowRoute, _toleranceReadbackRoute, _sealCompletionRoute, transportEmpty,
        _provenancePkg, _namePkg⟩ := carrier
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have windowUnary' : UnaryHistory window' := unary_transport windowUnary sameWindow
  have toleranceUnary' : UnaryHistory tolerance' := unary_transport toleranceUnary sameTolerance
  have readbackUnary' : UnaryHistory readback' := unary_transport readbackUnary sameReadback
  have sealUnary' : UnaryHistory sealRow' := unary_transport sealUnary sameSeal
  have completionUnary' : UnaryHistory completion' :=
    unary_transport completionUnary sameCompletion
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory route' := unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary sameName
  have transportEmpty' : hsame transport' BHist.Empty :=
    hsame_trans (hsame_symm sameTransport) transportEmpty
  exact
    ⟨sourceUnary', windowUnary', toleranceUnary', readbackUnary', sealUnary',
      completionUnary', transportUnary', routeUnary', provenanceUnary', nameUnary',
      sourceWindow', toleranceReadback', sealCompletion', transportEmpty',
      provenancePkg', namePkg'⟩

theorem CauchyCompletionUnitCarrier_dense_embedding_universal_route [AskSetup] [PackageSetup]
    {source window tolerance readback sealRow completion transport route provenance name
      denseRead universalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport route
        provenance name bundle pkg ->
      Cont completion route denseRead ->
        Cont denseRead route universalRead ->
          PkgSig bundle denseRead pkg ->
            PkgSig bundle universalRead pkg ->
              UnaryHistory source ∧ UnaryHistory completion ∧ UnaryHistory denseRead ∧
                UnaryHistory universalRead ∧ Cont source window tolerance ∧
                  Cont tolerance readback sealRow ∧ Cont sealRow route completion ∧
                    Cont completion route denseRead ∧ Cont denseRead route universalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle universalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier denseRoute universalRoute _densePkg universalPkg
  obtain ⟨sourceUnary, _windowUnary, _toleranceUnary, _readbackUnary, _sealUnary,
    completionUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
      sourceWindowRoute, toleranceReadbackRoute, sealCompletionRoute, _transportEmpty,
        provenancePkg, _namePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary routeUnary denseRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed denseUnary routeUnary universalRoute
  exact
    ⟨sourceUnary, completionUnary, denseUnary, universalUnary, sourceWindowRoute,
      toleranceReadbackRoute, sealCompletionRoute, denseRoute, universalRoute, provenancePkg,
      universalPkg⟩

end BEDC.Derived.CauchyCompletionUnitUp
