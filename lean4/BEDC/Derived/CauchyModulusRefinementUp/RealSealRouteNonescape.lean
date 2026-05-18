import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementRealSealRouteNonescape [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e sealRead ->
        PkgSig bundle sealRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                  hsame row sealRead)
              (fun row : BHist =>
                Cont t w q ∧ Cont q e sealRead ∧ hsame row sealRead)
              (fun row : BHist =>
                PkgSig bundle p pkg ∧ PkgSig bundle sealRead pkg ∧ hsame row sealRead)
              hsame ∧
            UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
              UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sealRoute sealPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have carrierWitness :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
            hsame row sealRead)
        (fun row : BHist => Cont t w q ∧ Cont q e sealRead ∧ hsame row sealRead)
        (fun row : BHist =>
          PkgSig bundle p pkg ∧ PkgSig bundle sealRead pkg ∧ hsame row sealRead)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead (And.intro carrierWitness (hsame_refl sealRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨twq, sealRoute, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨pPkg, sealPkg, source.right⟩
  }
  exact ⟨cert, wUnary, qUnary, eUnary, sealUnary⟩

end BEDC.Derived.CauchyModulusRefinementUp
