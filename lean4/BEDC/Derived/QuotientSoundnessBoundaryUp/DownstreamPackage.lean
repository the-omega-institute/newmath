import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_erased_derivation_refusal_certificate
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        PkgSig bundle refusalRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                hsame row refusalRead)
            (fun row : BHist =>
              Cont e a v ∧ Cont v t row ∧ PkgSig bundle refusalRead pkg)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle refusalRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal refusalPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    eAV, _eTH, _hCN, pPkg, _nPkg, _hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  exact {
    core := {
      carrier_inhabited := Exists.intro refusalRead
        (And.intro carrierWitness (hsame_refl refusalRead))
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
      exact
        ⟨eAV, cont_result_hsame_transport vTRefusal (hsame_symm source.right),
          refusalPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport refusalUnary (hsame_symm source.right), pPkg, refusalPkg⟩
  }

theorem QuotientSoundnessBoundary_transport_only_downstream_package
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            Cont consumer n ledgerRead ->
              PkgSig bundle refusalRead pkg ->
                PkgSig bundle transportRead pkg ->
                  PkgSig bundle consumer pkg ->
                    PkgSig bundle ledgerRead pkg ->
                      SemanticNameCert
                        (fun row : BHist =>
                          QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                            hsame row ledgerRead)
                        (fun row : BHist =>
                          Cont e a v ∧ Cont v t refusalRead ∧ Cont t h transportRead ∧
                            Cont h c consumer ∧ Cont consumer n row ∧
                              PkgSig bundle ledgerRead pkg)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                            PkgSig bundle ledgerRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport hCConsumer consumerNLedger _refusalPkg _transportPkg
    _consumerPkg ledgerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, nUnary,
    eAV, _eTH, _hCN, pPkg, nPkg, _hN⟩ := carrier
  have _refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have _transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed consumerUnary nUnary consumerNLedger
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
      exact
        ⟨eAV, vTRefusal, tHTransport, hCConsumer,
          cont_result_hsame_transport consumerNLedger (hsame_symm source.right),
          ledgerPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport ledgerUnary (hsame_symm source.right), pPkg, nPkg, ledgerPkg⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
