import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_gamma_critical_strip_readiness [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' publicRoot : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont transports' routes provenance' →
            Cont pole zeroLedger' gamma' →
              PkgSig bundle provenance' pkg →
                hsame eta eta' →
                  hsame zeroLedger zeroLedger' →
                    UnaryHistory routes →
                      UnaryHistory name →
                        Cont routes name publicRoot →
                          PkgSig bundle publicRoot pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row gamma ∧ UnaryHistory publicRoot)
                                (fun row : BHist =>
                                  hsame row gamma ∧ Cont pole zeroLedger' gamma')
                                (fun row : BHist =>
                                  PkgSig bundle provenance' pkg ∧
                                    PkgSig bundle publicRoot pkg ∧ hsame row gamma)
                                hsame ∧
                              hsame gamma gamma' ∧ UnaryHistory publicRoot ∧
                                hsame publicRoot (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary publicRoute publicPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := publicRoot)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary publicRoute
  obtain ⟨_analyticSame, _transportsSame, _provenanceSame, gammaSame, publicUnary,
    publicSame, _namePkg, provenancePkg'⟩ := readiness
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gamma ∧ UnaryHistory publicRoot)
          (fun row : BHist => hsame row gamma ∧ Cont pole zeroLedger' gamma')
          (fun row : BHist =>
            PkgSig bundle provenance' pkg ∧ PkgSig bundle publicRoot pkg ∧
              hsame row gamma)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro gamma ⟨hsame_refl gamma, publicUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    · intro _row source
      exact ⟨source.left, gammaRoute⟩
    · intro _row source
      exact ⟨provenancePkg', publicPkg, source.left⟩
  exact ⟨cert, gammaSame, publicUnary, publicSame⟩

end BEDC.Derived.ZetaContinuationWitnessUp
