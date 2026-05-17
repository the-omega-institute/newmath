import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_public_bridge_schema [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont transportRead n bridgeRead ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle bridgeRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                        Cont v t refusalRead ∧ Cont t h transportRead ∧
                          Cont transportRead n bridgeRead ∧ hsame row bridgeRead)
                    (fun row : BHist =>
                      Cont e a v ∧ Cont v t refusalRead ∧ Cont t h transportRead ∧
                        Cont transportRead n row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
                        PkgSig bundle transportRead pkg ∧ PkgSig bundle bridgeRead pkg ∧
                          hsame h n)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport transportNBridge refusalPkg transportPkg bridgePkg
  have sourceWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
        Cont v t refusalRead ∧ Cont t h transportRead ∧
          Cont transportRead n bridgeRead ∧ hsame bridgeRead bridgeRead :=
    ⟨carrier, vTRefusal, tHTransport, transportNBridge, hsame_refl bridgeRead⟩
  obtain ⟨_eUnary, _aUnary, tUnary, _vUnary, hUnary, _cUnary, _pUnary, nUnary, eAV,
    _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed (unary_cont_closed tUnary hUnary tHTransport) nUnary transportNBridge
  exact {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceWitness
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
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            source.right.right.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨eAV, source.right.left, source.right.right.left,
          cont_result_hsame_transport source.right.right.right.left
            (hsame_symm source.right.right.right.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport bridgeUnary (hsame_symm source.right.right.right.right),
          refusalPkg, transportPkg, bridgePkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
