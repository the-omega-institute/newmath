import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_public_export_route [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont locatedInterval continuousMap publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row locatedInterval ∨ hsame row continuousMap ∨
                  hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier locatedContinuousPublic publicPkg
  obtain ⟨locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    _localNameCertUnary, modulusBisectionNested, bisectionNestedReal, provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedReal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed locatedUnary continuousUnary locatedContinuousPublic
  have sourceAtPublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row locatedInterval ∨ hsame row continuousMap ∨
              hsame row nestedWindow ∨ hsame row realSeal ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.IntermediateValueUp
