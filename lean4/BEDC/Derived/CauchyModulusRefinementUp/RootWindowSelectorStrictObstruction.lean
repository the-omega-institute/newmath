import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_window_selector_strict_obstruction
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        Cont selected q readback →
          Cont readback e sealRead →
            Cont w sealRead terminalRead →
              PkgSig bundle terminalRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                        bundle pkg ∧ hsame row terminalRead)
                    (fun row : BHist =>
                      Cont t w selected ∧ Cont selected q readback ∧
                        Cont readback e sealRead ∧ Cont w sealRead row)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRead pkg)
                    hsame ∧
                  UnaryHistory selected ∧ UnaryHistory readback ∧
                    UnaryHistory sealRead ∧ UnaryHistory terminalRead ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier twSelected selectedQReadback readbackESealRead wSealTerminal terminalPkg
  have carrierPacket :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    carrier
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, hn⟩ :=
    carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary twSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESealRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed wUnary sealReadUnary wSealTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
              hsame row terminalRead)
          (fun row : BHist =>
            Cont t w selected ∧ Cont selected q readback ∧ Cont readback e sealRead ∧
              Cont w sealRead row)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro terminalRead ⟨carrierPacket, hsame_refl terminalRead⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact
        ⟨twSelected, selectedQReadback, readbackESealRead,
          cont_result_hsame_transport wSealTerminal (hsame_symm source.right)⟩
    · intro row source
      exact ⟨unary_transport terminalReadUnary (hsame_symm source.right), terminalPkg⟩
  exact ⟨cert, selectedUnary, readbackUnary, sealReadUnary, terminalReadUnary, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
