import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_formal_target_ledger [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' formalTarget : BHist}
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
                        Cont routes name formalTarget →
                          PkgSig bundle formalTarget pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  ZetaContinuationWitnessPacket basic eta analytic pole
                                    functional zeroLedger gamma transports routes provenance name
                                    bundle pkg ∧
                                  (hsame row analytic ∨ hsame row gamma ∨
                                    hsame row formalTarget))
                                (fun row : BHist =>
                                  hsame row analytic ∨ hsame row gamma ∨
                                    hsame row formalTarget)
                                (fun _row : BHist =>
                                  PkgSig bundle provenance' pkg ∧
                                    PkgSig bundle formalTarget pkg)
                                hsame ∧
                              hsame analytic analytic' ∧ hsame transports transports' ∧
                                hsame provenance provenance' ∧ hsame gamma gamma' ∧
                                  UnaryHistory formalTarget ∧
                                    hsame formalTarget (append routes name) ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle provenance' pkg ∧
                                          PkgSig bundle formalTarget pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary routesNameFormal formalTargetPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := formalTarget)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary routesNameFormal
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, formalTargetUnary,
    formalTargetSame, namePkg, provenancePkg'⟩ := readiness
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧
            (hsame row analytic ∨ hsame row gamma ∨ hsame row formalTarget))
          (fun row : BHist =>
            hsame row analytic ∨ hsame row gamma ∨ hsame row formalTarget)
          (fun _row : BHist =>
            PkgSig bundle provenance' pkg ∧ PkgSig bundle formalTarget pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro analytic
            ⟨packet, Or.inl (hsame_refl analytic)⟩
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
          constructor
          · exact source.left
          · cases source.right with
            | inl sameAnalytic =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameAnalytic)
            | inr rest =>
                cases rest with
                | inl sameGamma =>
                    exact Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) sameGamma))
                | inr sameFormal =>
                    exact Or.inr
                      (Or.inr (hsame_trans (hsame_symm sameRows) sameFormal))
      }
      pattern_sound := by
        intro _row source
        exact source.right
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg', formalTargetPkg⟩
    }
  exact
    ⟨cert, analyticSame, transportsSame, provenanceSame, gammaSame, formalTargetUnary,
      formalTargetSame, namePkg, provenancePkg', formalTargetPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
