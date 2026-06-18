import BEDC.Derived.CauchyCompletionMultiplicationUp.NameCertObligations

namespace BEDC.Derived.CauchyCompletionMultiplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMultiplicationCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {M O I A S R D E H C P N flattenRead sealRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMultiplicationCarrier M O I A S R D E H C P N bundle pkg ->
      Cont M O flattenRead ->
        Cont S R sealRead ->
          Cont sealRead E realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                      hsame row realRead)
                  (fun row : BHist =>
                    hsame row realRead ∧ Cont sealRead E realRead ∧
                      PkgSig bundle realRead pkg)
                  hsame ∧
                UnaryHistory flattenRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory realRead ∧ Cont M O flattenRead ∧
                    Cont S R sealRead ∧ Cont sealRead E realRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier flattenRoute sealRoute realRoute realPkg
  obtain ⟨mUnary, oUnary, _iUnary, _aUnary, sUnary, rUnary, _dUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _hM, _cP, provenancePkg, _namePkg⟩ := carrier
  have flattenUnary : UnaryHistory flattenRead :=
    unary_cont_closed mUnary oUnary flattenRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sUnary rUnary sealRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed sealUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
              hsame row realRead)
          (fun row : BHist =>
            hsame row realRead ∧ Cont sealRead E realRead ∧
              PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realRoute, realPkg⟩
  }
  exact
    ⟨cert, flattenUnary, sealUnary, realUnary, flattenRoute, sealRoute, realRoute,
      provenancePkg, realPkg⟩

end BEDC.Derived.CauchyCompletionMultiplicationUp
