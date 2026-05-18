import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundaryRefusalLedger [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead -> Cont t h transportRead ->
        PkgSig bundle refusalRead pkg -> PkgSig bundle transportRead pkg ->
          SemanticNameCert
            (fun row : BHist => QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
              hsame row transportRead)
            (fun row : BHist => Cont e a v ∧ Cont v t refusalRead ∧ Cont t h row)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg ∧
              PkgSig bundle refusalRead pkg ∧ PkgSig bundle transportRead pkg ∧ hsame h n)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport refusalPkg transportPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro transportRead ⟨carrierWitness, hsame_refl transportRead⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨eAV, vTRefusal,
        cont_result_hsame_transport tHTransport (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport transportUnary (hsame_symm source.right), pPkg, refusalPkg,
        transportPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
