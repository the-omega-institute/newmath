import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCarrier_independence_boundary [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead radiusRead siblingBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli fold
        precision transport route provenance localName bundle pkg →
      Cont source probes compactRead →
        Cont centers radii radiusRead →
          Cont radiusRead target siblingBoundary →
            PkgSig bundle siblingBoundary pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row siblingBoundary ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactRead ∨ hsame row radiusRead ∨
                      hsame row siblingBoundary ∨ Cont moduli fold precision)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle siblingBoundary pkg ∧
                      hsame row siblingBoundary)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory siblingBoundary ∧ Cont source probes compactRead ∧
                    Cont centers radii radiusRead ∧ Cont radiusRead target siblingBoundary ∧
                      Cont moduli fold precision ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle siblingBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier sourceProbesCompact centersRadiiRadius radiusTargetBoundary boundaryPkg
  obtain ⟨sourceUnary, targetUnary, _toleranceUnary, probesUnary, centersUnary, radiiUnary,
    _moduliUnary, _foldUnary, _precisionUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    carrierModuliFoldPrecision, _carrierPrecisionRouteName, provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centersUnary radiiUnary centersRadiiRadius
  have siblingBoundaryUnary : UnaryHistory siblingBoundary :=
    unary_cont_closed radiusReadUnary targetUnary radiusTargetBoundary
  have sourceBoundary :
      (fun row : BHist => hsame row siblingBoundary ∧ UnaryHistory row) siblingBoundary := by
    exact ⟨hsame_refl siblingBoundary, siblingBoundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactRead ∨ hsame row radiusRead ∨ hsame row siblingBoundary ∨
              Cont moduli fold precision)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle siblingBoundary pkg ∧
              hsame row siblingBoundary)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro siblingBoundary sourceBoundary
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, boundaryPkg, source.left⟩
  }
  exact
    ⟨cert, compactReadUnary, radiusReadUnary, siblingBoundaryUnary, sourceProbesCompact,
      centersRadiiRadius, radiusTargetBoundary, carrierModuliFoldPrecision, provenancePkg,
      boundaryPkg⟩

end BEDC.Derived.CompactNetModulusSelectorUp
