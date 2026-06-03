import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorFiniteNetExposure [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead radiusRead precisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg ->
      Cont source probes compactRead -> Cont centers radii radiusRead ->
        Cont fold precision precisionRead -> PkgSig bundle provenance pkg ->
          PkgSig bundle precisionRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row precisionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row probes ∨ hsame row centers ∨
                    hsame row radii ∨ hsame row compactRead ∨ hsame row radiusRead ∨
                      hsame row precisionRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle precisionRead pkg ∧
                    hsame row precisionRead)
                hsame ∧
              UnaryHistory compactRead ∧ UnaryHistory radiusRead ∧
                UnaryHistory precisionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute radiusRoute precisionRoute provenancePkg precisionReadPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, centersUnary,
    radiiUnary, _moduliUnary, foldUnary, precisionUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _carrierProvenancePkg⟩ :=
      carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary compactRoute
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centersUnary radiiUnary radiusRoute
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed foldUnary precisionUnary precisionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row precisionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row probes ∨ hsame row centers ∨
              hsame row radii ∨ hsame row compactRead ∨ hsame row radiusRead ∨
                hsame row precisionRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle precisionRead pkg ∧
              hsame row precisionRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro precisionRead ⟨hsame_refl precisionRead, precisionReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, precisionReadPkg, source.left⟩
  }
  exact ⟨cert, compactReadUnary, radiusReadUnary, precisionReadUnary⟩

end BEDC.Derived.CompactNetModulusSelectorUp
