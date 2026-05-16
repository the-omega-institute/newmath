import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_dependent_eliminator_refusal_certificate
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer dependentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            Cont consumer n dependentRead ->
              PkgSig bundle refusalRead pkg ->
                PkgSig bundle transportRead pkg ->
                  PkgSig bundle consumer pkg ->
                    PkgSig bundle dependentRead pkg ->
                      SemanticNameCert
                        (fun row : BHist =>
                          QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                            Cont v t refusalRead ∧ Cont t h transportRead ∧
                              Cont h c consumer ∧ Cont consumer n dependentRead ∧
                                hsame row dependentRead)
                        (fun row : BHist =>
                          Cont e a v ∧ Cont v t refusalRead ∧ Cont t h transportRead ∧
                            Cont h c consumer ∧ Cont consumer n row)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
                            PkgSig bundle transportRead pkg ∧ PkgSig bundle consumer pkg ∧
                              PkgSig bundle dependentRead pkg ∧ hsame h n)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport hCConsumer consumerNDependent
    refusalPkg transportPkg consumerPkg dependentPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, nUnary,
    eAV, _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have dependentUnary : UnaryHistory dependentRead :=
    unary_cont_closed consumerUnary nUnary consumerNDependent
  exact {
    core := {
      carrier_inhabited := Exists.intro dependentRead
        ⟨carrierWitness, vTRefusal, tHTransport, hCConsumer, consumerNDependent,
          hsame_refl dependentRead⟩
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
            source.right.right.right.left, source.right.right.right.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right.right.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨eAV, source.right.left, source.right.right.left,
          source.right.right.right.left,
          cont_result_hsame_transport consumerNDependent
            (hsame_symm source.right.right.right.right.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport dependentUnary (hsame_symm source.right.right.right.right.right),
          refusalPkg, transportPkg, consumerPkg, dependentPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
