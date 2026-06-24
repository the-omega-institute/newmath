import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorRequestObligationSurface [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName requestRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli fold
        precision transport route provenance localName bundle pkg ->
      Cont tolerance probes requestRead ->
        PkgSig bundle requestRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row requestRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row tolerance ∨ hsame row probes ∨ hsame row centers ∨
                  hsame row radii ∨ hsame row requestRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont tolerance probes requestRead ∧
                  PkgSig bundle requestRead pkg)
              hsame ∧
            UnaryHistory requestRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier toleranceProbesRequest requestPkg
  obtain ⟨_sourceUnary, _targetUnary, toleranceUnary, probesUnary, _centersUnary,
    _radiiUnary, _moduliUnary, _foldUnary, _precisionUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ := carrier
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed toleranceUnary probesUnary toleranceProbesRequest
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row requestRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tolerance ∨ hsame row probes ∨ hsame row centers ∨
              hsame row radii ∨ hsame row requestRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tolerance probes requestRead ∧
              PkgSig bundle requestRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro requestRead ⟨hsame_refl requestRead, requestReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceProbesRequest, requestPkg⟩
  }
  exact ⟨cert, requestReadUnary⟩

end BEDC.Derived.CompactNetModulusSelectorUp
