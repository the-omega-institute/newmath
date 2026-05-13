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

end BEDC.Derived.CompletionFunctorUp
