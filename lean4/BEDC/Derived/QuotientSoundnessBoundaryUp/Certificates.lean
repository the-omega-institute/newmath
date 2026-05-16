import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_fixed_classifier_certificate [AskSetup] [PackageSetup]
    {e a t v h c p n sourceRead transportRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      hsame sourceRead e ->
        Cont t h transportRead ->
          Cont h c consumerRead ->
            PkgSig bundle transportRead pkg ->
              PkgSig bundle consumerRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                      hsame row consumerRead)
                  (fun row : BHist =>
                    hsame sourceRead e ∧ Cont e t h ∧ Cont t h transportRead ∧
                      Cont h c row)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                      PkgSig bundle consumerRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceSame tHTransport hCConsumer _transportPkg consumerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, eTH, _hCN, pPkg, nPkg, _hN⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        (And.intro carrierWitness (hsame_refl consumerRead))
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
      exact ⟨sourceSame, eTH, tHTransport,
        cont_result_hsame_transport hCConsumer (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport consumerUnary (hsame_symm source.right), pPkg, nPkg,
        consumerPkg⟩
  }

theorem QuotientSoundnessBoundary_psame_transport_exhaustion_certificate
    [AskSetup] [PackageSetup]
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
                        hsame row ledgerRead)
                    (fun row : BHist =>
                      Cont v t refusalRead ∧ Cont t h transportRead ∧
                        Cont transportRead n row ∧ PkgSig bundle ledgerRead pkg)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle n pkg ∧ PkgSig bundle ledgerRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport transportNLedger _refusalPkg _transportPkg ledgerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, nUnary,
    _eAV, _eTH, _hCN, _pPkg, nPkg, _hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary nUnary transportNLedger
  exact {
    core := {
      carrier_inhabited := Exists.intro ledgerRead
        (And.intro carrierWitness (hsame_refl ledgerRead))
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
        cont_result_hsame_transport transportNLedger (hsame_symm source.right), ledgerPkg⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport ledgerUnary (hsame_symm source.right), nPkg, ledgerPkg⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
