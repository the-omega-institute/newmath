import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCarrier_uniformmodulus_handoff [AskSetup] [PackageSetup]
    {X Y E probes C R M F D H Q P N uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier X Y E probes C R M F D H Q P N bundle pkg ->
      Cont D Q uniformRead ->
        PkgSig bundle uniformRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row Y ∨ hsame row E ∨ hsame row probes ∨
                  hsame row C ∨ hsame row R ∨ hsame row M ∨ hsame row F ∨
                    hsame row D ∨ hsame row H ∨ hsame row Q ∨ hsame row P ∨
                      hsame row N ∨ hsame row uniformRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D Q uniformRead ∧
                  PkgSig bundle uniformRead pkg)
              hsame ∧
            UnaryHistory D ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: CompactNetModulusSelectorCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier uniformRoute uniformPkg
  obtain ⟨_sourceUnary, _targetUnary, _toleranceUnary, _probesUnary, _centersUnary,
    _radiiUnary, _moduliUnary, _foldUnary, precisionUnary, _transportUnary, routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ := carrier
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed precisionUnary routeUnary uniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row E ∨ hsame row probes ∨
              hsame row C ∨ hsame row R ∨ hsame row M ∨ hsame row F ∨
                hsame row D ∨ hsame row H ∨ hsame row Q ∨ hsame row P ∨
                  hsame row N ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Q uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, uniformRoute, uniformPkg⟩
  }
  exact ⟨cert, precisionUnary, uniformUnary⟩

end BEDC.Derived.CompactNetModulusSelectorUp
