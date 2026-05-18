import BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusWitnessLedgerCarrier_bridge_request_surface
    [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail
                  dyadic readback sealRow transport route provenance name bundle pkg ∧
                hsame row bridgeRead)
            (fun row : BHist =>
              Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                Cont dyadic readback sealRow ∧ Cont sealRow transport row)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sealTransportBridge bridgePkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg := carrier
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    _dyadicUnary, readbackUnary, sealUnary, transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed witnessUnary windowUnary witnessWindowNormalizer
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed normalizerUnary tailUnary normalizerTailDyadic
  have _sealUnaryFromRoute : UnaryHistory sealRow :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackSeal
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sealUnary transportUnary sealTransportBridge
  exact {
    core := {
      carrier_inhabited := Exists.intro bridgeRead
        (And.intro carrierWitness (hsame_refl bridgeRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
          cont_result_hsame_transport sealTransportBridge (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport bridgeUnary (hsame_symm source.right), bridgePkg⟩
  }

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
