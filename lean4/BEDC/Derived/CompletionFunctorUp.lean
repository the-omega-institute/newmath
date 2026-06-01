import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionFunctorCarrier [AskSetup] [PackageSetup]
    (monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory monad ∧ UnaryHistory universal ∧ UnaryHistory realCompletion ∧
    UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory denseMap ∧
      UnaryHistory extension ∧ UnaryHistory functorLedger ∧ UnaryHistory transport ∧
        UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont monad universal realCompletion ∧ Cont source target denseMap ∧
            Cont denseMap extension functorLedger ∧ Cont functorLedger transport routes ∧
              Cont transport routes provenance ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg

theorem CompletionFunctorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CompletionFunctorCarrier monad universal realCompletion source target denseMap
            extension functorLedger transport routes provenance name bundle pkg ∧
            hsame row provenance)
        (fun row : BHist =>
          CompletionFunctorCarrier monad universal realCompletion source target denseMap
            extension functorLedger transport routes provenance name bundle pkg ∧
            hsame row provenance)
        (fun row : BHist =>
          CompletionFunctorCarrier monad universal realCompletion source target denseMap
            extension functorLedger transport routes provenance name bundle pkg ∧
            hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro carrier (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CompletionFunctorCarrier_public_extension_interface [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont denseMap extension extensionRead ->
        hsame extensionRead functorLedger ->
          UnaryHistory denseMap ∧ UnaryHistory extension ∧ UnaryHistory functorLedger ∧
            UnaryHistory extensionRead ∧ Cont denseMap extension functorLedger ∧
              Cont denseMap extension extensionRead ∧ hsame extensionRead functorLedger ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  intro carrier extensionReadRow sameExtensionRead
  obtain ⟨_monadUnary, _universalUnary, _realCompletionUnary, _sourceUnary, _targetUnary,
    denseMapUnary, extensionUnary, functorLedgerUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, _monadicCompletion, _denseMapRow, functorLedgerRow,
    _functorTransportRow, _transportProvenanceRow, provenanceSig, nameSig⟩ := carrier
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed denseMapUnary extensionUnary extensionReadRow
  exact
    ⟨denseMapUnary, extensionUnary, functorLedgerUnary, extensionReadUnary, functorLedgerRow,
      extensionReadRow, sameExtensionRead, provenanceSig, nameSig⟩

theorem CompletionFunctorCarrier_unit_boundary [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name unitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont source target unitRead ->
        hsame unitRead denseMap ->
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory denseMap ∧
            UnaryHistory unitRead ∧ Cont source target denseMap ∧
              Cont source target unitRead ∧ hsame unitRead denseMap ∧
                Cont monad universal realCompletion ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg := by
  intro carrier unitRoute sameUnit
  obtain ⟨_monadUnary, _universalUnary, _realCompletionUnary, sourceUnary, targetUnary,
    denseMapUnary, _extensionUnary, _functorLedgerUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, monadRoute, denseMapRoute, _extensionRoute,
    _functorRoute, _transportRoute, provenanceSig, nameSig⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed sourceUnary targetUnary unitRoute
  exact
    ⟨sourceUnary, targetUnary, denseMapUnary, unitUnary, denseMapRoute, unitRoute,
      sameUnit, monadRoute, provenanceSig, nameSig⟩

theorem CompletionFunctorCarrier_extension_ledger_exactness [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont denseMap extension extensionRead ->
        hsame extensionRead functorLedger ->
          UnaryHistory denseMap ∧ UnaryHistory extension ∧ UnaryHistory functorLedger ∧
            UnaryHistory extensionRead ∧ Cont denseMap extension functorLedger ∧
              Cont denseMap extension extensionRead ∧ hsame extensionRead functorLedger ∧
                PkgSig bundle provenance pkg := by
  intro carrier extensionReadRow sameExtensionRead
  rcases carrier with
    ⟨_monadUnary, _universalUnary, _realCompletionUnary, _sourceUnary, _targetUnary,
      denseMapUnary, extensionUnary, functorLedgerUnary, _transportUnary, _routesUnary,
      _provenanceUnary, _nameUnary, _monadUniversalRealCompletion, _sourceTargetDenseMap,
      denseMapExtensionFunctorLedger, _functorLedgerTransportRoutes,
      _transportRoutesProvenance, provenancePkg, _namePkg⟩
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed denseMapUnary extensionUnary extensionReadRow
  exact
    ⟨denseMapUnary, extensionUnary, functorLedgerUnary, extensionReadUnary,
      denseMapExtensionFunctorLedger, extensionReadRow, sameExtensionRead, provenancePkg⟩

theorem CompletionFunctorCarrier_identity_route_stability [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name identityLedger identityRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont denseMap extension identityLedger ->
        hsame identityLedger functorLedger ->
          Cont identityLedger transport identityRoute ->
            hsame identityRoute routes ->
              UnaryHistory denseMap ∧ UnaryHistory extension ∧ UnaryHistory identityLedger ∧
                UnaryHistory identityRoute ∧ Cont denseMap extension identityLedger ∧
                  hsame identityLedger functorLedger ∧
                    Cont identityLedger transport identityRoute ∧ hsame identityRoute routes ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  intro carrier identityLedgerRow sameIdentityLedger identityRouteRow sameIdentityRoute
  obtain ⟨_monadUnary, _universalUnary, _realCompletionUnary, _sourceUnary, _targetUnary,
    denseMapUnary, extensionUnary, _functorLedgerUnary, transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, _monadUniversalRealCompletion, _sourceTargetDenseMap,
    _denseMapExtensionFunctorLedger, _functorLedgerTransportRoutes,
    _transportRoutesProvenance, provenanceSig, nameSig⟩ := carrier
  have identityLedgerUnary : UnaryHistory identityLedger :=
    unary_cont_closed denseMapUnary extensionUnary identityLedgerRow
  have identityRouteUnary : UnaryHistory identityRoute :=
    unary_cont_closed identityLedgerUnary transportUnary identityRouteRow
  exact
    ⟨denseMapUnary, extensionUnary, identityLedgerUnary, identityRouteUnary,
      identityLedgerRow, sameIdentityLedger, identityRouteRow, sameIdentityRoute,
      provenanceSig, nameSig⟩

theorem CompletionFunctorCarrier_completion_consumer_surface [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport routes
      provenance name unitRead extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont source target unitRead ->
        hsame unitRead denseMap ->
          Cont denseMap extension extensionRead ->
            hsame extensionRead functorLedger ->
              UnaryHistory unitRead ∧ UnaryHistory extensionRead ∧
                Cont source target denseMap ∧ Cont denseMap extension functorLedger ∧
                  hsame unitRead denseMap ∧ hsame extensionRead functorLedger ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  intro carrier unitRoute sameUnit extensionReadRow sameExtensionRead
  have unitFacts :
      UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory denseMap ∧
        UnaryHistory unitRead ∧ Cont source target denseMap ∧ Cont source target unitRead ∧
          hsame unitRead denseMap ∧ Cont monad universal realCompletion ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg :=
    CompletionFunctorCarrier_unit_boundary carrier unitRoute sameUnit
  have extensionFacts :
      UnaryHistory denseMap ∧ UnaryHistory extension ∧ UnaryHistory functorLedger ∧
        UnaryHistory extensionRead ∧ Cont denseMap extension functorLedger ∧
          Cont denseMap extension extensionRead ∧ hsame extensionRead functorLedger ∧
            PkgSig bundle provenance pkg :=
    CompletionFunctorCarrier_extension_ledger_exactness carrier extensionReadRow sameExtensionRead
  obtain ⟨_sourceUnary, _targetUnary, _denseMapUnary, unitReadUnary, sourceTargetDenseMap,
    _unitReadRoute, sameUnitRead, _monadRoute, provenancePkg, namePkg⟩ := unitFacts
  obtain ⟨_denseMapUnaryExt, _extensionUnary, _functorLedgerUnary, extensionReadUnary,
    denseMapExtensionFunctorLedger, _extensionReadRoute, sameExtensionReadLedger,
    _extensionProvenancePkg⟩ := extensionFacts
  exact
    ⟨unitReadUnary, extensionReadUnary, sourceTargetDenseMap, denseMapExtensionFunctorLedger,
      sameUnitRead, sameExtensionReadLedger, provenancePkg, namePkg⟩

theorem CompletionFunctorCarrier_public_completion_export [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name unitRead extensionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont source target unitRead ->
        hsame unitRead denseMap ->
          Cont denseMap extension extensionRead ->
            hsame extensionRead functorLedger ->
              Cont extensionRead routes publicRead ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row unitRead ∨ hsame row extensionRead ∨
                          hsame row publicRead ∨ hsame row provenance ∨ hsame row name)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory unitRead ∧ UnaryHistory extensionRead ∧
                      UnaryHistory publicRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unitRoute sameUnit extensionReadRoute sameExtensionRead publicRoute publicPkg
  have consumerSurface :
      UnaryHistory unitRead ∧ UnaryHistory extensionRead ∧
        Cont source target denseMap ∧ Cont denseMap extension functorLedger ∧
          hsame unitRead denseMap ∧ hsame extensionRead functorLedger ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg :=
    CompletionFunctorCarrier_completion_consumer_surface carrier unitRoute sameUnit
      extensionReadRoute sameExtensionRead
  obtain ⟨unitUnary, extensionReadUnary, _sourceTargetDenseMap,
    _denseMapExtensionFunctorLedger, _sameUnitRead, _sameExtensionReadLedger,
    provenancePkg, namePkg⟩ := consumerSurface
  obtain ⟨_monadUnary, _universalUnary, _realCompletionUnary, _sourceUnary, _targetUnary,
    _denseMapUnary, _extensionUnary, _functorLedgerUnary, _transportUnary, routesUnary,
    _provenanceUnary, _nameUnary, _monadRoute, _denseMapRoute, _extensionLedgerRoute,
    _functorTransportRoute, _transportProvenanceRoute, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed extensionReadUnary routesUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row unitRead ∨ hsame row extensionRead ∨ hsame row publicRead ∨
            hsame row provenance ∨ hsame row name)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro (hsame_refl publicRead) publicUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        have samePublic : hsame row' publicRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have rowUnary : UnaryHistory row' :=
          unary_transport source.right sameRows
        exact And.intro samePublic rowUnary
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact And.intro source.right (And.intro provenancePkg publicPkg)
  }
  exact ⟨cert, unitUnary, extensionReadUnary, publicUnary, provenancePkg, namePkg⟩

theorem CompletionFunctorCarrier_composition_route_stability [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name firstLedger secondLedger compositeRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont denseMap extension firstLedger ->
        hsame firstLedger functorLedger ->
          Cont firstLedger transport secondLedger ->
            hsame secondLedger routes ->
              Cont denseMap extension compositeRoute ->
                hsame compositeRoute functorLedger ->
                  UnaryHistory firstLedger /\ UnaryHistory secondLedger /\
                    UnaryHistory compositeRoute /\ Cont denseMap extension firstLedger /\
                      Cont firstLedger transport secondLedger /\
                        Cont denseMap extension compositeRoute /\
                          hsame firstLedger functorLedger /\ hsame secondLedger routes /\
                            hsame compositeRoute functorLedger /\
                              PkgSig bundle provenance pkg /\ PkgSig bundle name pkg := by
  intro carrier firstLedgerRow sameFirstLedger secondLedgerRow sameSecondLedger
    compositeRouteRow sameCompositeRoute
  obtain ⟨_monadUnary, _universalUnary, _realCompletionUnary, _sourceUnary, _targetUnary,
    denseMapUnary, extensionUnary, _functorLedgerUnary, transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, _monadUniversalRealCompletion, _sourceTargetDenseMap,
    _denseMapExtensionFunctorLedger, _functorLedgerTransportRoutes,
    _transportRoutesProvenance, provenancePkg, namePkg⟩ := carrier
  have firstLedgerUnary : UnaryHistory firstLedger :=
    unary_cont_closed denseMapUnary extensionUnary firstLedgerRow
  have secondLedgerUnary : UnaryHistory secondLedger :=
    unary_cont_closed firstLedgerUnary transportUnary secondLedgerRow
  have compositeRouteUnary : UnaryHistory compositeRoute :=
    unary_cont_closed denseMapUnary extensionUnary compositeRouteRow
  exact
    ⟨firstLedgerUnary, secondLedgerUnary, compositeRouteUnary, firstLedgerRow,
      secondLedgerRow, compositeRouteRow, sameFirstLedger, sameSecondLedger,
      sameCompositeRoute, provenancePkg, namePkg⟩

theorem CompletionFunctorCarrier_functoriality [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name unitRead firstLedger secondLedger compositeRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont source target unitRead ->
        hsame unitRead denseMap ->
          Cont denseMap extension firstLedger ->
            hsame firstLedger functorLedger ->
              Cont firstLedger transport secondLedger ->
                hsame secondLedger routes ->
                  Cont denseMap extension compositeRoute ->
                    hsame compositeRoute functorLedger ->
                      UnaryHistory unitRead ∧ UnaryHistory firstLedger ∧
                        UnaryHistory secondLedger ∧ UnaryHistory compositeRoute ∧
                          Cont source target denseMap ∧
                            Cont denseMap extension functorLedger ∧
                              Cont source target unitRead ∧
                                Cont denseMap extension firstLedger ∧
                                  Cont firstLedger transport secondLedger ∧
                                    Cont denseMap extension compositeRoute ∧
                                      hsame unitRead denseMap ∧
                                        hsame firstLedger functorLedger ∧
                                          hsame secondLedger routes ∧
                                            hsame compositeRoute functorLedger ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier unitRoute sameUnit firstLedgerRoute sameFirstLedger secondLedgerRoute
    sameSecondLedger compositeRouteRow sameCompositeRoute
  obtain ⟨_monadUnary, _universalUnary, _realCompletionUnary, sourceUnary, targetUnary,
    denseMapUnary, extensionUnary, _functorLedgerUnary, transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, _monadUniversalRealCompletion, sourceTargetDenseMap,
    denseMapExtensionFunctorLedger, _functorLedgerTransportRoutes,
    _transportRoutesProvenance, provenancePkg, namePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed sourceUnary targetUnary unitRoute
  have firstLedgerUnary : UnaryHistory firstLedger :=
    unary_cont_closed denseMapUnary extensionUnary firstLedgerRoute
  have secondLedgerUnary : UnaryHistory secondLedger :=
    unary_cont_closed firstLedgerUnary transportUnary secondLedgerRoute
  have compositeRouteUnary : UnaryHistory compositeRoute :=
    unary_cont_closed denseMapUnary extensionUnary compositeRouteRow
  exact
    ⟨unitUnary, firstLedgerUnary, secondLedgerUnary, compositeRouteUnary,
      sourceTargetDenseMap, denseMapExtensionFunctorLedger, unitRoute, firstLedgerRoute,
      secondLedgerRoute, compositeRouteRow, sameUnit, sameFirstLedger, sameSecondLedger,
      sameCompositeRoute, provenancePkg, namePkg⟩

theorem CompletionFunctorCarrier_scoped_dependency_spine [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name unitRead extensionRead identityRoute compositeRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont source target unitRead ->
        hsame unitRead denseMap ->
          Cont denseMap extension extensionRead ->
            hsame extensionRead functorLedger ->
              Cont extensionRead transport identityRoute ->
                hsame identityRoute routes ->
                  Cont denseMap extension compositeRoute ->
                    hsame compositeRoute functorLedger ->
                      UnaryHistory monad ∧ UnaryHistory universal ∧
                        UnaryHistory realCompletion ∧ UnaryHistory unitRead ∧
                          UnaryHistory extensionRead ∧ UnaryHistory identityRoute ∧
                            UnaryHistory compositeRoute ∧ Cont monad universal realCompletion ∧
                              Cont source target denseMap ∧
                                Cont denseMap extension functorLedger ∧
                                  Cont functorLedger transport routes ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier unitRoute _sameUnit extensionReadRoute _sameExtensionRead identityRouteRow
    _sameIdentityRoute compositeRouteRow _sameCompositeRoute
  obtain ⟨monadUnary, universalUnary, realCompletionUnary, sourceUnary, targetUnary,
    denseMapUnary, extensionUnary, _functorLedgerUnary, transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, monadUniversalRealCompletion, sourceTargetDenseMap,
    denseMapExtensionFunctorLedger, functorLedgerTransportRoutes,
    _transportRoutesProvenance, provenancePkg, namePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed sourceUnary targetUnary unitRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed denseMapUnary extensionUnary extensionReadRoute
  have identityRouteUnary : UnaryHistory identityRoute :=
    unary_cont_closed extensionReadUnary transportUnary identityRouteRow
  have compositeRouteUnary : UnaryHistory compositeRoute :=
    unary_cont_closed denseMapUnary extensionUnary compositeRouteRow
  exact
    ⟨monadUnary, universalUnary, realCompletionUnary, unitUnary, extensionReadUnary,
      identityRouteUnary, compositeRouteUnary, monadUniversalRealCompletion,
      sourceTargetDenseMap, denseMapExtensionFunctorLedger, functorLedgerTransportRoutes,
      provenancePkg, namePkg⟩

theorem CompletionFunctorCarrier_cauchy_seal_composition [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name firstSeal secondSeal composedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      Cont source target firstSeal ->
        Cont firstSeal realCompletion secondSeal ->
          Cont secondSeal target composedSeal ->
            PkgSig bundle composedSeal pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row composedSeal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row firstSeal ∨ hsame row secondSeal ∨
                      hsame row composedSeal ∨ hsame row realCompletion ∨ hsame row target)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle composedSeal pkg)
                  hsame ∧
                UnaryHistory firstSeal ∧ UnaryHistory secondSeal ∧
                  UnaryHistory composedSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier firstRoute secondRoute composedRoute composedPkg
  obtain ⟨_monadUnary, _universalUnary, realCompletionUnary, sourceUnary, targetUnary,
    _denseMapUnary, _extensionUnary, _functorLedgerUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, _monadUniversalRealCompletion, _sourceTargetDenseMap,
    _denseMapExtensionFunctorLedger, _functorLedgerTransportRoutes,
    _transportRoutesProvenance, provenancePkg, _namePkg⟩ := carrier
  have firstSealUnary : UnaryHistory firstSeal :=
    unary_cont_closed sourceUnary targetUnary firstRoute
  have secondSealUnary : UnaryHistory secondSeal :=
    unary_cont_closed firstSealUnary realCompletionUnary secondRoute
  have composedSealUnary : UnaryHistory composedSeal :=
    unary_cont_closed secondSealUnary targetUnary composedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row composedSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row firstSeal ∨ hsame row secondSeal ∨ hsame row composedSeal ∨
            hsame row realCompletion ∨ hsame row target)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle composedSeal pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro composedSeal (And.intro (hsame_refl composedSeal) composedSealUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        have sameComposed : hsame row' composedSeal :=
          hsame_trans (hsame_symm sameRows) source.left
        have rowUnary : UnaryHistory row' :=
          unary_transport source.right sameRows
        exact And.intro sameComposed rowUnary
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact And.intro source.right (And.intro provenancePkg composedPkg)
  }
  exact ⟨cert, firstSealUnary, secondSealUnary, composedSealUnary, provenancePkg⟩

end BEDC.Derived.CompletionFunctorUp
