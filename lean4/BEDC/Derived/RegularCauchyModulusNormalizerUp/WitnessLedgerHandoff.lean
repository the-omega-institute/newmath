import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_witness_ledger_handoff [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont meet dyadic witnessRead →
        PkgSig bundle witnessRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                  sealRow transport route provenance name bundle pkg ∧ hsame row witnessRead)
            (fun row : BHist => Cont meet dyadic row ∧ UnaryHistory row)
            (fun row : BHist => hsame row witnessRead ∧ PkgSig bundle witnessRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier meetDyadicWitness witnessPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, meetUnary, _windowUnary,
    dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _sourceMeet, _meetWindowDyadic, _dyadicReadbackSeal,
    _sealTransportRoute, _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed meetUnary dyadicUnary meetDyadicWitness
  have sourceAtWitness :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧ hsame witnessRead witnessRead :=
    And.intro carrierWitness (hsame_refl witnessRead)
  exact {
    core := {
      carrier_inhabited := Exists.intro witnessRead sourceAtWitness
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
      exact
        ⟨cont_result_hsame_transport meetDyadicWitness (hsame_symm source.right),
          unary_transport witnessUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, witnessPkg⟩
  }

end BEDC.Derived.RegularCauchyModulusNormalizerUp
