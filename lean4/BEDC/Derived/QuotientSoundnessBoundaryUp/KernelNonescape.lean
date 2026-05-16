import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_kernel_nonescape [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont v t refusalRead →
        Cont t h transportRead →
          Cont transportRead n kernelRead →
            PkgSig bundle refusalRead pkg →
              PkgSig bundle kernelRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                      hsame row kernelRead)
                  (fun row : BHist =>
                    Cont v t refusalRead ∧ Cont t h transportRead ∧
                      Cont transportRead n row ∧ PkgSig bundle kernelRead pkg)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                      PkgSig bundle kernelRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport transportNKernel _refusalPkg kernelPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, _vUnary, hUnary, _cUnary, _pUnary, nUnary,
    _eAV, _eTH, _hCN, pPkg, nPkg, _hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed transportUnary nUnary transportNKernel
  exact {
    core := {
      carrier_inhabited := Exists.intro kernelRead
        (And.intro carrierWitness (hsame_refl kernelRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨vTRefusal, tHTransport,
        cont_result_hsame_transport transportNKernel (hsame_symm source.right),
        kernelPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport kernelUnary (hsame_symm source.right), pPkg, nPkg,
        kernelPkg⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
