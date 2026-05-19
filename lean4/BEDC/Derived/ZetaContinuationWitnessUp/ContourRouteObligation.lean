import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_contour_route_obligation [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      etaPrime analyticPrime transportsPrime provenancePrime contourRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont basic etaPrime analyticPrime →
        Cont analyticPrime functional transportsPrime →
          Cont transportsPrime routes provenancePrime →
            Cont functional gamma contourRead →
              PkgSig bundle provenancePrime pkg →
                PkgSig bundle contourRead pkg →
                  hsame eta etaPrime →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row analyticPrime ∨ hsame row transportsPrime ∨
                            hsame row contourRead)
                        (fun _row : BHist =>
                          Cont basic etaPrime analyticPrime ∧
                            Cont analyticPrime functional transportsPrime ∧
                              Cont functional gamma contourRead)
                        (fun _row : BHist =>
                          PkgSig bundle provenancePrime pkg ∧ PkgSig bundle contourRead pkg)
                        hsame ∧
                      hsame analytic analyticPrime ∧ hsame transports transportsPrime ∧
                        hsame provenance provenancePrime ∧ Cont functional gamma contourRead ∧
                          Cont transportsPrime routes provenancePrime ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle contourRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet basicEtaRoute analyticTransportRoute transportProvenanceRoute
    functionalGammaContour provenancePrimePkg contourPkg etaSame
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := etaPrime) (analytic' := analyticPrime)
      (transports' := transportsPrime) (provenance' := provenancePrime)
      (bundle := bundle) (pkg := pkg) packet basicEtaRoute analyticTransportRoute
      transportProvenanceRoute provenancePrimePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, _provenancePkg⟩ :=
    ledger
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row analyticPrime ∨ hsame row transportsPrime ∨ hsame row contourRead)
          (fun _row : BHist =>
            Cont basic etaPrime analyticPrime ∧
              Cont analyticPrime functional transportsPrime ∧
                Cont functional gamma contourRead)
          (fun _row : BHist =>
            PkgSig bundle provenancePrime pkg ∧ PkgSig bundle contourRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro analyticPrime (Or.inl (hsame_refl analyticPrime))
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
        cases source with
        | inl sameAnalytic =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameAnalytic)
        | inr rest =>
            cases rest with
            | inl sameTransports =>
                exact Or.inr
                  (Or.inl (hsame_trans (hsame_symm sameRows) sameTransports))
            | inr sameContour =>
                exact Or.inr
                  (Or.inr (hsame_trans (hsame_symm sameRows) sameContour))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨basicEtaRoute, analyticTransportRoute, functionalGammaContour⟩
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePrimePkg, contourPkg⟩
  }
  exact
    ⟨cert, analyticSame, transportsSame, provenanceSame, functionalGammaContour,
      transportProvenanceRoute, namePkg, contourPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
