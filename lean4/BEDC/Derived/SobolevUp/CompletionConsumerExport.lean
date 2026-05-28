import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_completion_consumer_export [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      completionRead traceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont base codomain completionRead ->
        Cont gradient localCert traceRead ->
          PkgSig bundle completionRead pkg ->
            PkgSig bundle traceRead pkg ->
              SemanticNameCert
                    (fun row : BHist =>
                      hsame row completionRead ∨ hsame row traceRead ∨ hsame row gradient)
                    (fun row : BHist => UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧
                        (hsame row completionRead ∨ hsame row traceRead ∨ hsame row gradient))
                    hsame ∧
                  UnaryHistory completionRead ∧ UnaryHistory traceRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier completionRoute traceRoute _completionPkg _tracePkg
  obtain ⟨_domainUnary, baseUnary, codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, localCertUnary, _domainBaseCodomain,
    _codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed baseUnary codomainUnary completionRoute
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed gradientUnary localCertUnary traceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row completionRead ∨ hsame row traceRead ∨ hsame row gradient)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧
              (hsame row completionRead ∨ hsame row traceRead ∨ hsame row gradient))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead (Or.inl (hsame_refl completionRead))
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
        cases source with
        | inl sameCompletion =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameCompletion)
        | inr rest =>
            cases rest with
            | inl sameTrace =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTrace))
            | inr sameGradient =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameGradient))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameCompletion =>
          exact unary_transport completionUnary (hsame_symm sameCompletion)
      | inr rest =>
          cases rest with
          | inl sameTrace =>
              exact unary_transport traceUnary (hsame_symm sameTrace)
          | inr sameGradient =>
              exact unary_transport gradientUnary (hsame_symm sameGradient)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source⟩
  }
  exact ⟨cert, completionUnary, traceUnary⟩

end BEDC.Derived.SobolevUp
