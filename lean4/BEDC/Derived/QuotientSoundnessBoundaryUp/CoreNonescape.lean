import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_non_escape [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont v h refusalRead →
        Cont h c consumerRead →
          PkgSig bundle refusalRead pkg →
            PkgSig bundle consumerRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                    hsame row consumerRead)
                (fun row : BHist =>
                  Cont e a v ∧ Cont v h refusalRead ∧ Cont h c row ∧
                    PkgSig bundle consumerRead pkg)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
                    PkgSig bundle consumerRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vHRefusal hCConsumer refusalPkg consumerPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, _pPkg, _nPkg, _hN⟩ := carrier
  have vUnary : UnaryHistory v := unary_cont_closed eUnary aUnary eAV
  have _refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary vHRefusal
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
      exact
        ⟨eAV, vHRefusal,
          cont_result_hsame_transport hCConsumer (hsame_symm source.right),
          consumerPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport consumerUnary (hsame_symm source.right), refusalPkg,
          consumerPkg⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
