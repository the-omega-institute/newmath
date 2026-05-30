import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_scoped_route_package [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont transports' routes provenance' ->
            Cont pole zeroLedger' gamma' ->
              PkgSig bundle provenance' pkg ->
                hsame eta eta' ->
                  hsame zeroLedger zeroLedger' ->
                    UnaryHistory routes ->
                      UnaryHistory name ->
                        Cont routes name scopedRead ->
                          PkgSig bundle scopedRead pkg ->
                            SemanticNameCert
                              (fun row : BHist =>
                                ZetaContinuationWitnessPacket basic eta analytic pole functional
                                  zeroLedger gamma transports routes provenance name bundle pkg ∧
                                  hsame row scopedRead)
                              (fun row : BHist =>
                                hsame row scopedRead ∧ UnaryHistory scopedRead ∧
                                  hsame gamma gamma')
                              (fun row : BHist =>
                                PkgSig bundle provenance' pkg ∧ PkgSig bundle scopedRead pkg ∧
                                  hsame row scopedRead ∧ Cont pole zeroLedger' gamma')
                              hsame ∧
                            hsame analytic analytic' ∧ hsame transports transports' ∧
                              hsame provenance provenance' ∧ hsame gamma gamma' ∧
                                UnaryHistory scopedRead ∧
                                  hsame scopedRead (append routes name) ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle provenance' pkg ∧
                                        PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary routesNameScoped scopedPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := scopedRead)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary routesNameScoped
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, scopedUnary,
    scopedSame, namePkg, provenancePkg'⟩ := readiness
  have sourceScoped :
      (fun row : BHist =>
        ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
          transports routes provenance name bundle pkg ∧ hsame row scopedRead) scopedRead := by
    exact ⟨packet, hsame_refl scopedRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧ hsame row scopedRead)
          (fun row : BHist =>
            hsame row scopedRead ∧ UnaryHistory scopedRead ∧ hsame gamma gamma')
          (fun row : BHist =>
            PkgSig bundle provenance' pkg ∧ PkgSig bundle scopedRead pkg ∧
              hsame row scopedRead ∧ Cont pole zeroLedger' gamma')
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro scopedRead sourceScoped
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, scopedUnary, gammaSame⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg', scopedPkg, source.right, gammaRoute⟩
    }
  exact
    ⟨cert, analyticSame, transportsSame, provenanceSame, gammaSame, scopedUnary,
      scopedSame, namePkg, provenancePkg', scopedPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
