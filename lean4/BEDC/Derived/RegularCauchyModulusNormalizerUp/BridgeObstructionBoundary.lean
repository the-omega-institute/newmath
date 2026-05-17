import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_bridge_obstruction_boundary [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont route provenance bridgeRead →
        PkgSig bundle bridgeRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                    readback sealRow transport route provenance name bundle pkg ∧
                  hsame row bridgeRead)
              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont muX muY meet ∧ Cont meet window dyadic ∧
                  Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
                    Cont route provenance row ∧ PkgSig bundle row pkg)
              hsame ∧
            UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier routeProvenanceBridge bridgePkg
  have carrierWitness := carrier
  rcases carrier with
    ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, _windowUnary, _dyadicUnary,
      _readbackUnary, _sealUnary, _transportUnary, routeUnary, provenanceUnary, _nameUnary,
      sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
      _routeProvenanceName, _meetPkg, _namePkg⟩
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceBridge
  have sourceAtBridge :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
          transport route provenance name bundle pkg ∧
        hsame bridgeRead bridgeRead :=
    ⟨carrierWitness, hsame_refl bridgeRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                sealRow transport route provenance name bundle pkg ∧
              hsame row bridgeRead)
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont muX muY meet ∧ Cont meet window dyadic ∧ Cont dyadic readback sealRow ∧
              Cont sealRow transport route ∧ Cont route provenance row ∧
                PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceAtBridge
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, unary_transport bridgeUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      cases source.right
      exact
        ⟨sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
          routeProvenanceBridge, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
