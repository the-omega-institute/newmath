import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_public_contour_gamma_separation [AskSetup]
    [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' contourRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont pole zeroLedger' gamma' →
        hsame zeroLedger zeroLedger' →
          Cont functional gamma' contourRead →
            PkgSig bundle contourRead pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row gamma' ∨ hsame row contourRead)
                    (fun _row : BHist =>
                      Cont functional gamma' contourRead ∧
                        Cont transports routes provenance)
                    (fun _row : BHist =>
                      PkgSig bundle contourRead pkg ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                hsame gamma gamma' ∧ Cont functional gamma' contourRead ∧
                  Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle contourRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert Cont hsame
  intro packet gammaRoute zeroLedgerSame functionalGammaContour contourPkg
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, namePkg, provenancePkg⟩ := gammaBoundary
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    transportsRoutesProvenance, _namePkg, _provenancePkg⟩ := packet
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gamma' ∨ hsame row contourRead)
          (fun _row : BHist =>
            Cont functional gamma' contourRead ∧ Cont transports routes provenance)
          (fun _row : BHist =>
            PkgSig bundle contourRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro gamma' (Or.inl (hsame_refl gamma'))
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
          cases source with
          | inl sameGamma =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameGamma)
          | inr sameContour =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameContour)
      }
      pattern_sound := by
        intro _row _source
        exact ⟨functionalGammaContour, transportsRoutesProvenance⟩
      ledger_sound := by
        intro _row _source
        exact ⟨contourPkg, provenancePkg⟩
    }
  exact
    ⟨cert, gammaSame, functionalGammaContour, transportsRoutesProvenance, namePkg,
      contourPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
