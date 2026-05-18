import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_root_zero_ledger_totality [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' zeroRead : BHist}
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
                        Cont routes name zeroRead ->
                          PkgSig bundle zeroRead pkg ->
                            SemanticNameCert
                              (fun row : BHist =>
                                ZetaContinuationWitnessPacket basic eta analytic pole
                                  functional zeroLedger gamma transports routes provenance name
                                  bundle pkg /\ hsame row zeroLedger)
                              (fun row : BHist => hsame row zeroLedger /\
                                Cont pole zeroLedger' gamma')
                              (fun row : BHist =>
                                PkgSig bundle provenance' pkg /\
                                  PkgSig bundle zeroRead pkg /\ hsame row zeroLedger)
                              hsame /\
                            hsame gamma gamma' /\ UnaryHistory zeroRead /\
                              hsame zeroRead (append routes name) /\
                                PkgSig bundle name pkg /\
                                  PkgSig bundle provenance' pkg /\
                                    PkgSig bundle zeroRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary routesNameZeroRead zeroReadPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := zeroRead)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary routesNameZeroRead
  obtain ⟨_analyticSame, _transportsSame, _provenanceSame, gammaSame, zeroReadUnary,
    zeroReadSame, namePkg, provenancePkg'⟩ := readiness
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
            transports routes provenance name bundle pkg /\ hsame row zeroLedger)
        (fun row : BHist => hsame row zeroLedger /\ Cont pole zeroLedger' gamma')
        (fun row : BHist =>
          PkgSig bundle provenance' pkg /\ PkgSig bundle zeroRead pkg /\
            hsame row zeroLedger)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro zeroLedger ⟨packet, hsame_refl zeroLedger⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' sameRows
        exact hsame_symm sameRows
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    · intro _row source
      exact ⟨source.right, gammaRoute⟩
    · intro _row source
      exact ⟨provenancePkg', zeroReadPkg, source.right⟩
  exact
    ⟨cert, gammaSame, zeroReadUnary, zeroReadSame, namePkg, provenancePkg',
      zeroReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
