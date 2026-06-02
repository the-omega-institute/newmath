import BEDC.Derived.CompletionFunctorUp

namespace BEDC.Derived.CompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompletionFunctorCarrier_non_escape [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      (hsame publicRead monad ∨ hsame publicRead universal ∨
        hsame publicRead realCompletion ∨ hsame publicRead source ∨
          hsame publicRead target ∨ hsame publicRead denseMap ∨
            hsame publicRead extension ∨ hsame publicRead functorLedger ∨
              hsame publicRead transport ∨ hsame publicRead routes ∨
                hsame publicRead provenance ∨ hsame publicRead name) ->
        UnaryHistory publicRead ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: CompletionFunctorCarrier BHist ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier publicMember
  rcases carrier with
    ⟨monadUnary, universalUnary, realCompletionUnary, sourceUnary, targetUnary,
      denseMapUnary, extensionUnary, functorLedgerUnary, transportUnary, routesUnary,
      provenanceUnary, nameUnary, _monadRoute, _denseMapRoute, _extensionRoute,
      _functorRoute, _transportRoute, provenancePkg, namePkg⟩
  have publicUnary : UnaryHistory publicRead := by
    rcases publicMember with hMonad | hUniversal | hRealCompletion | hSource | hTarget |
      hDenseMap | hExtension | hFunctorLedger | hTransport | hRoutes | hProvenance | hName
    · exact unary_transport monadUnary (hsame_symm hMonad)
    · exact unary_transport universalUnary (hsame_symm hUniversal)
    · exact unary_transport realCompletionUnary (hsame_symm hRealCompletion)
    · exact unary_transport sourceUnary (hsame_symm hSource)
    · exact unary_transport targetUnary (hsame_symm hTarget)
    · exact unary_transport denseMapUnary (hsame_symm hDenseMap)
    · exact unary_transport extensionUnary (hsame_symm hExtension)
    · exact unary_transport functorLedgerUnary (hsame_symm hFunctorLedger)
    · exact unary_transport transportUnary (hsame_symm hTransport)
    · exact unary_transport routesUnary (hsame_symm hRoutes)
    · exact unary_transport provenanceUnary (hsame_symm hProvenance)
    · exact unary_transport nameUnary (hsame_symm hName)
  exact ⟨publicUnary, provenancePkg, namePkg⟩

end BEDC.Derived.CompletionFunctorUp
