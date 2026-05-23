import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCarrier_fold_soundness [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead modulusRead precisionRead foldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg ->
      Cont source probes compactRead ->
        Cont moduli fold modulusRead ->
          Cont precision route precisionRead ->
            Cont modulusRead precision foldRead ->
              PkgSig bundle foldRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      CompactNetModulusSelectorCarrier source target tolerance probes centers
                          radii moduli fold precision transport route provenance localName
                          bundle pkg ∧
                        hsame row foldRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        (hsame row compactRead ∨ hsame row modulusRead ∨
                          hsame row precisionRead ∨ hsame row foldRead))
                    (fun _row : BHist =>
                      Cont source probes compactRead ∧ Cont moduli fold modulusRead ∧
                        Cont precision route precisionRead ∧
                          Cont modulusRead precision foldRead ∧ PkgSig bundle foldRead pkg)
                    hsame ∧
                  UnaryHistory compactRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory precisionRead ∧ UnaryHistory foldRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier sourceProbesCompact moduliFoldModulus precisionRouteRead
    modulusPrecisionFold foldReadPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, _centersUnary,
    _radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed moduliUnary foldUnary moduliFoldModulus
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteRead
  have foldReadUnary : UnaryHistory foldRead :=
    unary_cont_closed modulusReadUnary precisionUnary modulusPrecisionFold
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CompactNetModulusSelectorCarrier source target tolerance probes centers radii
                moduli fold precision transport route provenance localName bundle pkg ∧
              hsame row foldRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row compactRead ∨ hsame row modulusRead ∨ hsame row precisionRead ∨
                hsame row foldRead))
          (fun _row : BHist =>
            Cont source probes compactRead ∧ Cont moduli fold modulusRead ∧
              Cont precision route precisionRead ∧ Cont modulusRead precision foldRead ∧
                PkgSig bundle foldRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro foldRead
        ⟨carrierWitness, hsame_refl foldRead⟩
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
        intro _row _other sameRows sourceRow
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨unary_transport foldReadUnary (hsame_symm sourceRow.right),
        Or.inr (Or.inr (Or.inr sourceRow.right))⟩
    ledger_sound := by
      intro _row _sourceRow
      exact
        ⟨sourceProbesCompact, moduliFoldModulus, precisionRouteRead, modulusPrecisionFold,
          foldReadPkg⟩
  }
  exact ⟨cert, compactReadUnary, modulusReadUnary, precisionReadUnary, foldReadUnary⟩

end BEDC.Derived.CompactNetModulusSelectorUp
