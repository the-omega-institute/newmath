import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_unblock_package [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c rootRead ->
        PkgSig bundle rootRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                  hsame row n)
              (fun row : BHist => hsame row n ∧ UnaryHistory row ∧ Cont h c rootRead)
              (fun _row : BHist => PkgSig bundle p pkg ∧ PkgSig bundle rootRead pkg)
              hsame ∧
            UnaryHistory rootRead ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
              Cont q e h ∧ Cont h c rootRead ∧ PkgSig bundle p pkg ∧
                PkgSig bundle rootRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier rootRoute rootPkg
  have carrierPacket :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    carrier
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed hUnary cUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
              hsame row n)
          (fun row : BHist => hsame row n ∧ UnaryHistory row ∧ Cont h c rootRead)
          (fun _row : BHist => PkgSig bundle p pkg ∧ PkgSig bundle rootRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro n ⟨carrierPacket, hsame_refl n⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact
        ⟨source.right, unary_transport nUnary (hsame_symm source.right), rootRoute⟩
    · intro _row _source
      exact ⟨pPkg, rootPkg⟩
  exact
    ⟨cert, rootUnary, m0m1u, uvt, twq, qeh, rootRoute, pPkg, rootPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
