import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_comparison_stability [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      comparisonRead comparisonRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont window dyadic comparisonRead ->
        hsame comparisonRead comparisonRead' ->
          PkgSig bundle comparisonRead pkg ->
            UnaryHistory comparisonRead' ∧ Cont window dyadic comparisonRead' ∧
              SemanticNameCert
                (fun row : BHist =>
                  RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                      readback sealRow transport route provenance name bundle pkg ∧
                    hsame row comparisonRead')
                (fun row : BHist => hsame row comparisonRead' ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont window dyadic row ∧ PkgSig bundle comparisonRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier windowDyadicComparison sameComparison comparisonPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, windowUnary, dyadicUnary,
    _readbackUnary, _sealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, _sourceMeet, _meetWindowDyadic, _dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicComparison
  have comparisonPrimeUnary : UnaryHistory comparisonRead' :=
    unary_transport comparisonUnary sameComparison
  have windowDyadicComparisonPrime : Cont window dyadic comparisonRead' :=
    cont_result_hsame_transport windowDyadicComparison sameComparison
  have sourceAtComparisonPrime :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame comparisonRead' comparisonRead' :=
    And.intro carrierWitness (hsame_refl comparisonRead')
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
              sealRow transport route provenance name bundle pkg ∧
            hsame row comparisonRead')
        (fun row : BHist => hsame row comparisonRead' ∧ UnaryHistory row)
        (fun row : BHist => Cont window dyadic row ∧ PkgSig bundle comparisonRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro comparisonRead' sourceAtComparisonPrime
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
      exact ⟨source.right, unary_transport comparisonPrimeUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport windowDyadicComparisonPrime (hsame_symm source.right),
          comparisonPkg⟩
  }
  exact ⟨comparisonPrimeUnary, windowDyadicComparisonPrime, cert⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
