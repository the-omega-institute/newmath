import BEDC.Derived.ZetaContinuationWitnessUp.PublicSourceLockExport

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_public_root_completion [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' publicRoot sourceLock criticalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont transports' routes provenance' ->
            PkgSig bundle provenance' pkg ->
              hsame eta eta' ->
                UnaryHistory routes ->
                  UnaryHistory name ->
                    Cont routes name publicRoot ->
                      Cont basic analytic' sourceLock ->
                        PkgSig bundle sourceLock pkg ->
                          Cont routes name criticalRead ->
                            PkgSig bundle criticalRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    ZetaContinuationWitnessPacket basic eta analytic pole
                                      functional zeroLedger gamma transports routes provenance name
                                      bundle pkg ∧ hsame row publicRoot)
                                  (fun row : BHist => hsame row publicRoot ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg ∧
                                      PkgSig bundle sourceLock pkg ∧
                                        PkgSig bundle criticalRead pkg ∧
                                          hsame row publicRoot)
                                  hsame ∧
                                UnaryHistory publicRoot ∧
                                  hsame publicRoot (append routes name) ∧
                                    hsame analytic analytic' ∧ hsame transports transports' ∧
                                      hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame routesUnary
    nameUnary routesNamePublic basicAnalyticSource sourceLockPkg routesNameCritical
    criticalReadPkg
  have exported :=
    ZetaContinuationWitnessPacket_public_source_lock_export
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance') (publicRoot := publicRoot)
      (sourceLock := sourceLock) (bundle := bundle) (pkg := pkg) packet basicRoute
      functionalRoute provenanceRoute provenancePkg etaSame routesUnary nameUnary
      routesNamePublic basicAnalyticSource sourceLockPkg
  obtain ⟨analyticSame, transportsSame, provenanceSame, publicRootUnary, publicRootRoute,
    _sourceLockRoute, namePkg, provenancePkg', sourceLockPkg'⟩ := exported
  have sourcePublic :
      (fun row : BHist =>
        ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
          transports routes provenance name bundle pkg ∧ hsame row publicRoot) publicRoot := by
    exact ⟨packet, hsame_refl publicRoot⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧ hsame row publicRoot)
          (fun row : BHist => hsame row publicRoot ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance' pkg ∧
              PkgSig bundle sourceLock pkg ∧ PkgSig bundle criticalRead pkg ∧
                hsame row publicRoot)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRoot sourcePublic
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, unary_transport publicRootUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨namePkg, provenancePkg', sourceLockPkg', criticalReadPkg, source.right⟩
    }
  exact
    ⟨cert, publicRootUnary, publicRootRoute, analyticSame, transportsSame,
      provenanceSame⟩

end BEDC.Derived.ZetaContinuationWitnessUp
