import BEDC.Derived.CauchyCompletionMultiplicationUp.NameCertObligations
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionMultiplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMultiplicationProvenanceExhaustion [AskSetup] [PackageSetup]
    {M O I A S R D E H C P N nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMultiplicationCarrier M O I A S R D E H C P N bundle pkg ->
      Cont P N nameRead ->
        PkgSig bundle nameRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row P ∨ hsame row N ∨ hsame row nameRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle nameRead pkg)
              hsame ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier nameRoute namePkg
  obtain ⟨_mUnary, _oUnary, _iUnary, _aUnary, _sUnary, _rUnary, _dUnary, _eUnary,
    _hUnary, _cUnary, pUnary, nUnary, _hM, _cP, provenancePkg, localNamePkg⟩ := carrier
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed pUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row P ∨ hsame row N ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
              PkgSig bundle nameRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, namePkg⟩
  }
  exact ⟨cert, nameUnary⟩

end BEDC.Derived.CauchyCompletionMultiplicationUp
