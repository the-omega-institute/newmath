import BEDC.Derived.ContourSumWindowUp.NameCertObligations
import BEDC.Derived.ContourSumWindowUp.OutputSealNonescape
import BEDC.Derived.ContourSumWindowUp.RefinementStability
import BEDC.Derived.ContourSumWindowUp.ResidueBoundary
import BEDC.Derived.ContourSumWindowUp.SubdivisionExactness

namespace BEDC.Derived.ContourSumWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContourSumWindowObligationClosurePackage [AskSetup] [PackageSetup]
    {contour holomorphic subdivision riemann output transport continuation provenance name
      ledgerRead outputRead residueRead outputSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContourSumWindowCarrier contour holomorphic subdivision riemann output transport
        continuation provenance name bundle pkg →
      Cont subdivision riemann ledgerRead →
        Cont ledgerRead output outputRead →
          Cont output continuation residueRead →
            Cont riemann output outputSeal →
              Cont outputSeal provenance publicRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle outputRead pkg →
                    PkgSig bundle publicRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row outputRead ∨ hsame row residueRead ∨
                              hsame row publicRead) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row contour ∨ hsame row holomorphic ∨
                              hsame row subdivision ∨ hsame row riemann ∨
                                hsame row output ∨ hsame row outputRead ∨
                                  hsame row residueRead ∨ hsame row publicRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle outputRead pkg ∧ PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory outputRead ∧ UnaryHistory residueRead ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier ledgerRoute outputRoute residueRoute outputSealRoute publicRoute
    _provenancePkg outputPkg publicPkg
  obtain ⟨_contourUnary, _holomorphicUnary, subdivisionUnary, riemannUnary, outputUnary,
    _transportUnary, continuationUnary, provenanceUnary, _nameUnary, _carrierSubdivision,
    _carrierOutput, _carrierContinuation, provenancePkg, _namePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed subdivisionUnary riemannUnary ledgerRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed ledgerUnary outputUnary outputRoute
  have residueUnary : UnaryHistory residueRead :=
    unary_cont_closed outputUnary continuationUnary residueRoute
  have outputSealUnary : UnaryHistory outputSeal :=
    unary_cont_closed riemannUnary outputUnary outputSealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputSealUnary provenanceUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row outputRead ∨ hsame row residueRead ∨ hsame row publicRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row contour ∨ hsame row holomorphic ∨ hsame row subdivision ∨
              hsame row riemann ∨ hsame row output ∨ hsame row outputRead ∨
                hsame row residueRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle outputRead pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead
          ⟨Or.inr (Or.inr (hsame_refl publicRead)), publicUnary⟩
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
        constructor
        · cases source.left with
          | inl sameOutput =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameOutput)
          | inr rest =>
              cases rest with
              | inl sameResidue =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameResidue))
              | inr samePublic =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) samePublic))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameOutput =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameOutput)))))
      | inr rest =>
          cases rest with
          | inl sameResidue =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameResidue))))))
          | inr samePublic =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr samePublic))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, outputPkg, publicPkg⟩
  }
  exact ⟨cert, outputReadUnary, residueUnary, publicUnary⟩

end BEDC.Derived.ContourSumWindowUp
