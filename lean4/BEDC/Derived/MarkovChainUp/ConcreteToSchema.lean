import BEDC.Derived.MarkovChainUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MarkovChainUp_concrete_to_schema [AskSetup] [PackageSetup]
    {prob random law transition controw provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            MarkovChainBHistTransitionCarrier prob random law transition controw provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            hsame row prob ∨ hsame row random ∨ hsame row law ∨
              hsame row transition ∨ hsame row controw ∨ hsame row provenance ∨
                hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont random transition controw ∧ Cont prob law provenance ∧
              Cont provenance controw endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        hsame endpoint (append provenance controw) := by
  -- BEDC touchpoint anchor: MarkovChainBHistTransitionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierSource :
      MarkovChainBHistTransitionCarrier prob random law transition controw provenance endpoint
        bundle pkg := carrier
  obtain ⟨_probUnary, _randomUnary, _lawUnary, _transitionUnary, _controwUnary,
    _provenanceUnary, endpointUnary, controwRoute, provenanceRoute, endpointRoute,
    endpointPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            MarkovChainBHistTransitionCarrier prob random law transition controw provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            hsame row prob ∨ hsame row random ∨ hsame row law ∨
              hsame row transition ∨ hsame row controw ∨ hsame row provenance ∨
                hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont random transition controw ∧ Cont prob law provenance ∧
              Cont provenance controw endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨carrierSource, hsame_refl endpoint⟩
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
      right
      right
      right
      right
      right
      right
      exact source.right
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.right), controwRoute,
          provenanceRoute, endpointRoute, endpointPkg⟩
  }
  exact ⟨cert, endpointRoute⟩

end BEDC.Derived.MarkovChainUp
