import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_shared_tail_meet_determinacy [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont meet dyadic leftRead ->
        Cont meet dyadic rightRead ->
          PkgSig bundle leftRead pkg ->
            PkgSig bundle rightRead pkg ->
              hsame leftRead rightRead ∧ UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                SemanticNameCert
                  (fun row : BHist =>
                    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                        readback sealRow transport route provenance name bundle pkg ∧
                      hsame row leftRead)
                  (fun row : BHist => Cont meet dyadic row ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row rightRead ∧ PkgSig bundle leftRead pkg ∧
                      PkgSig bundle rightRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier meetDyadicLeft meetDyadicRight leftPkg rightPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, meetUnary, _windowUnary,
    dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _sourceMeet, _meetWindowDyadic, _dyadicReadbackSeal,
    _sealTransportRoute, _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have sameRead : hsame leftRead rightRead :=
    cont_determinacy_up_to_hsame_spine meetDyadicLeft meetDyadicRight
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed meetUnary dyadicUnary meetDyadicLeft
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed meetUnary dyadicUnary meetDyadicRight
  have sourceAtLeft :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame leftRead leftRead :=
    And.intro carrierWitness (hsame_refl leftRead)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
              sealRow transport route provenance name bundle pkg ∧
            hsame row leftRead)
        (fun row : BHist => Cont meet dyadic row ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row rightRead ∧ PkgSig bundle leftRead pkg ∧ PkgSig bundle rightRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro leftRead sourceAtLeft
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
        ⟨cont_result_hsame_transport meetDyadicLeft (hsame_symm source.right),
          unary_transport leftUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨hsame_trans source.right sameRead, leftPkg, rightPkg⟩
  }
  exact ⟨sameRead, leftUnary, rightUnary, cert⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
