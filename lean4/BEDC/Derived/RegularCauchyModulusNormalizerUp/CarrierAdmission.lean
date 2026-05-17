import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_carrier_admission [AskSetup] [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      PkgSig bundle name pkg →
        SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                sealRow transport route provenance name bundle pkg ∧
              hsame row name)
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun _row : BHist =>
            UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
              UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
                  UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                    Cont muX muY meet ∧ Cont meet window dyadic ∧
                      Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
                        Cont route provenance name ∧ PkgSig bundle name pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier namePkg
  have carrierWitness := carrier
  obtain ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
    readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
    sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
    routeProvenanceName, _carrierMeetPkg, _carrierNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro name (And.intro carrierWitness (hsame_refl name))
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
        ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
          readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
          sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
          routeProvenanceName, namePkg⟩
  }

end BEDC.Derived.RegularCauchyModulusNormalizerUp
