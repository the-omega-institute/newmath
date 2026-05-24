import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_source_binding_strict_obstruction
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 u rootRead →
        Cont q e sealRead →
          PkgSig bundle rootRead pkg →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                      bundle pkg ∧ hsame row u)
                  (fun row : BHist => hsame row u ∧ Cont m0 m1 u ∧ Cont u v t)
                  (fun row : BHist =>
                    hsame row u ∧ PkgSig bundle p pkg ∧ Cont q e sealRead)
                  hsame ∧
                UnaryHistory rootRead ∧ UnaryHistory sealRead ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier m0URoot qESeal _rootPkg _sealPkg
  have carrierPacket :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    carrier
  obtain ⟨m0Unary, _m1Unary, uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, qeh, pPkg, hn⟩ :=
    carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed m0Unary uUnary m0URoot
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary qESeal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
              hsame row u)
          (fun row : BHist => hsame row u ∧ Cont m0 m1 u ∧ Cont u v t)
          (fun row : BHist => hsame row u ∧ PkgSig bundle p pkg ∧ Cont q e sealRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro u ⟨carrierPacket, hsame_refl u⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨source.right, m0m1u, uvt⟩
    · intro row source
      exact ⟨source.right, pPkg, qESeal⟩
  exact ⟨cert, rootUnary, sealUnary, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
