import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_normalized_route_bridge [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transportRow routeRow provenance name
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transportRow routeRow provenance name bundle pkg ->
      Cont routeRow provenance bridge ->
        PkgSig bundle bridge pkg ->
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                    sealRow transportRow routeRow provenance name bundle pkg ∧
                  hsame row bridge)
              (fun row : BHist => hsame row bridge ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont muX muY meet ∧ Cont meet window dyadic ∧ Cont dyadic readback sealRow ∧
                  Cont sealRow transportRow routeRow ∧ Cont routeRow provenance row ∧
                    PkgSig bundle row pkg)
              hsame ∧
            UnaryHistory bridge := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier routeProvenanceBridge bridgePkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, _windowUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, routeUnary, provenanceUnary,
    _nameUnary, sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
    _routeProvenanceName, _meetPkg, _namePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceBridge
  have sourceAtBridge :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
          transportRow routeRow provenance name bundle pkg ∧
        hsame bridge bridge :=
    And.intro carrierWitness (hsame_refl bridge)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                sealRow transportRow routeRow provenance name bundle pkg ∧
              hsame row bridge)
          (fun row : BHist => hsame row bridge ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont muX muY meet ∧ Cont meet window dyadic ∧ Cont dyadic readback sealRow ∧
              Cont sealRow transportRow routeRow ∧ Cont routeRow provenance row ∧
                PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridge sourceAtBridge
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨source.right, unary_transport bridgeUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      have routeRowForRow : Cont routeRow provenance row :=
        cont_result_hsame_transport routeProvenanceBridge (hsame_symm source.right)
      cases source.right
      exact
        ⟨sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
          routeRowForRow, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
