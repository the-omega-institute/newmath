import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_transport_refusal_normal_form
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            Cont consumer n ledgerRead ->
              PkgSig bundle ledgerRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                      hsame row ledgerRead)
                  (fun row : BHist =>
                    Cont e a v ∧ Cont v t refusalRead ∧ Cont t h transportRead ∧
                      Cont h c consumer ∧ Cont consumer n row)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle ledgerRead pkg ∧ hsame h n)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier vTRefusal tHTransport hCConsumer consumerNLedger ledgerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, nUnary, eAV,
    _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
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
          cont_result_hsame_transport consumerNLedger (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport ledgerUnary (hsame_symm source.right), ledgerPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
