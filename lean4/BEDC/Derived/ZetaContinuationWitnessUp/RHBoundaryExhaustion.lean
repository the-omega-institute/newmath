import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_rh_boundary_exhaustion [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' criticalRead gammaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg ->
      Cont pole zeroLedger' gamma' ->
        hsame zeroLedger zeroLedger' ->
          UnaryHistory routes ->
            UnaryHistory name ->
              Cont routes name criticalRead ->
                Cont routes name gammaRead ->
                  PkgSig bundle criticalRead pkg ->
                    PkgSig bundle gammaRead pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            ZetaContinuationWitnessPacket basic eta analytic pole functional
                                zeroLedger gamma transports routes provenance name bundle pkg ∧
                              (hsame row criticalRead ∨ hsame row gammaRead))
                          (fun row : BHist =>
                            hsame row criticalRead ∨ hsame row gammaRead)
                          (fun _row : BHist =>
                            Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle provenance pkg ∧
                                (PkgSig bundle criticalRead pkg ∨ PkgSig bundle gammaRead pkg))
                          hsame ∧
                        UnaryHistory criticalRead ∧ UnaryHistory gammaRead ∧ hsame gamma gamma' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet poleZeroGamma zeroLedgerSame routesUnary nameUnary routesNameCritical
    routesNameGamma criticalPkg gammaPkg
  have packetWitness := packet
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary routesNameCritical
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed routesUnary nameUnary routesNameGamma
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packetWitness poleZeroGamma zeroLedgerSame
  obtain ⟨gammaSame, _namePkgBoundary, _provenancePkgBoundary⟩ := gammaBoundary
  have sourceCritical :
      (fun row : BHist =>
        ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
            transports routes provenance name bundle pkg ∧
          (hsame row criticalRead ∨ hsame row gammaRead))
        criticalRead := by
    exact ⟨packetWitness, Or.inl (hsame_refl criticalRead)⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
                transports routes provenance name bundle pkg ∧
              (hsame row criticalRead ∨ hsame row gammaRead))
          (fun row : BHist => hsame row criticalRead ∨ hsame row gammaRead)
          (fun _row : BHist =>
            Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
              PkgSig bundle provenance pkg ∧
                (PkgSig bundle criticalRead pkg ∨ PkgSig bundle gammaRead pkg))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro criticalRead sourceCritical
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
          intro row other sameRows source
          rcases source with ⟨packetSource, rowMembership⟩
          have otherMembership :
              hsame other criticalRead ∨ hsame other gammaRead := by
            cases rowMembership with
            | inl rowCritical =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) rowCritical)
            | inr rowGamma =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) rowGamma)
          exact ⟨packetSource, otherMembership⟩
      }
      pattern_sound := by
        intro _row source
        exact source.right
      ledger_sound := by
        intro _row source
        cases source.right with
        | inl _rowCritical =>
            exact ⟨transportsRoutesProvenance, namePkg, provenancePkg, Or.inl criticalPkg⟩
        | inr _rowGamma =>
            exact ⟨transportsRoutesProvenance, namePkg, provenancePkg, Or.inr gammaPkg⟩
    }
  exact ⟨cert, criticalUnary, gammaReadUnary, gammaSame⟩

end BEDC.Derived.ZetaContinuationWitnessUp
