import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_mature_witness_ledger_handoff [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      witnessRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont readback sealRow witnessRead ->
        Cont witnessRead transport completionRead ->
          PkgSig bundle witnessRead pkg ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                      readback sealRow transport route provenance name bundle pkg ∧
                    hsame row completionRead)
                (fun row : BHist =>
                  Cont muX muY meet ∧ Cont meet window dyadic ∧
                    Cont dyadic readback sealRow ∧ Cont readback sealRow witnessRead ∧
                      Cont witnessRead transport row ∧ PkgSig bundle completionRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier readbackSealWitness witnessTransportCompletion _witnessPkg completionPkg
  rcases carrier with
    ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
      readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
      sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
      routeProvenanceName, meetPkg, namePkg⟩
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealWitness
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed witnessUnary transportUnary witnessTransportCompletion
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead (And.intro
          ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
            readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary,
            nameUnary, sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
            routeProvenanceName, meetPkg, namePkg⟩
          (hsame_refl completionRead))
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
      exact
        ⟨sourceMeet, meetWindowDyadic, dyadicReadbackSeal, readbackSealWitness,
          cont_result_hsame_transport witnessTransportCompletion (hsame_symm source.right),
          completionPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport completionUnary (hsame_symm source.right), completionPkg⟩
  }

end BEDC.Derived.RegularCauchyModulusNormalizerUp
