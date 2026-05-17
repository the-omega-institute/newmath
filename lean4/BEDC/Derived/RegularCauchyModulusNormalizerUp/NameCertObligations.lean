import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name audit :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont route provenance audit →
        PkgSig bundle audit pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                    readback sealRow transport route provenance name bundle pkg ∧
                  hsame row name)
              (fun row : BHist => hsame row name ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont muX muY meet ∧ Cont meet window dyadic ∧
                  Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
                    Cont route provenance audit ∧ PkgSig bundle meet pkg ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle audit pkg)
              hsame ∧
            UnaryHistory audit := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier routeProvenanceAudit auditPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, _windowUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, routeUnary, provenanceUnary,
    nameUnary, sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
    _routeProvenanceName, meetPkg, namePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceAudit
  have sourceAtName :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame name name :=
    And.intro carrierWitness (hsame_refl name)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                readback sealRow transport route provenance name bundle pkg ∧
              hsame row name)
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont muX muY meet ∧ Cont meet window dyadic ∧
              Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
                Cont route provenance audit ∧ PkgSig bundle meet pkg ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle audit pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name sourceAtName
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
      intro _row source
      exact ⟨source.right, unary_transport nameUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row _source
      exact
        ⟨sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
          routeProvenanceAudit, meetPkg, namePkg, auditPkg⟩
  }
  exact ⟨cert, auditUnary⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
