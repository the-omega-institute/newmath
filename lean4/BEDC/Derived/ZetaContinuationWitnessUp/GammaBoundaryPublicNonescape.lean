import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_gamma_boundary_public_nonescape
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' gammaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont pole zeroLedger' gamma' →
        hsame zeroLedger zeroLedger' →
          UnaryHistory routes →
            UnaryHistory name →
              Cont routes name gammaRead →
                PkgSig bundle gammaRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row gamma' ∨ hsame row gammaRead)
                      (fun row : BHist => hsame row gamma' ∨ hsame row gammaRead)
                      (fun _row : BHist =>
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle gammaRead pkg)
                      hsame ∧
                    hsame gamma gamma' ∧ UnaryHistory gammaRead ∧
                      hsame gammaRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet gammaRoute zeroLedgerSame routesUnary nameUnary routesNameGamma gammaReadPkg
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, namePkg, provenancePkg⟩ := gammaBoundary
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed routesUnary nameUnary routesNameGamma
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gamma' ∨ hsame row gammaRead)
          (fun row : BHist => hsame row gamma' ∨ hsame row gammaRead)
          (fun _row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle gammaRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gamma' (Or.inl (hsame_refl gamma'))
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
        | inl sameGamma =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameGamma)
        | inr sameRead =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameRead)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row _source
      exact ⟨namePkg, provenancePkg, gammaReadPkg⟩
  }
  exact ⟨cert, gammaSame, gammaReadUnary, routesNameGamma⟩

end BEDC.Derived.ZetaContinuationWitnessUp
