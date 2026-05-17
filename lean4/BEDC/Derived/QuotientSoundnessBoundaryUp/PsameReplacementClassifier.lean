import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_psame_replacement_classifier [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont transportRead n ledgerRead ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                        Cont v t refusalRead ∧ hsame row ledgerRead)
                    (fun row : BHist =>
                      Cont e t h ∧ Cont t h transportRead ∧ Cont transportRead n row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                        PkgSig bundle ledgerRead pkg ∧ hsame h n)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport transportNLedger _refusalPkg _transportPkg ledgerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, _vUnary, hUnary, _cUnary, _pUnary, nUnary,
    _eAV, eTH, _hCN, pPkg, nPkg, hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary nUnary transportNLedger
  exact {
    core := {
      carrier_inhabited := Exists.intro ledgerRead
        (And.intro carrierWitness (And.intro vTRefusal (hsame_refl ledgerRead)))
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
          ⟨source.left, source.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨eTH, tHTransport,
          cont_result_hsame_transport transportNLedger (hsame_symm source.right.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport ledgerUnary (hsame_symm source.right.right), pPkg, nPkg,
          ledgerPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
