import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_root_downstream_unblock_surface
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont v t refusalRead →
        Cont t h transportRead →
          Cont h c consumer →
            PkgSig bundle refusalRead pkg →
              PkgSig bundle transportRead pkg →
                PkgSig bundle consumer pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                        Cont v t refusalRead ∧ Cont t h transportRead ∧
                          Cont h c consumer ∧ hsame row consumer)
                    (fun row : BHist =>
                      Cont e a v ∧ Cont e t h ∧ Cont v t refusalRead ∧
                        Cont t h transportRead ∧ Cont h c row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                        PkgSig bundle refusalRead pkg ∧ PkgSig bundle transportRead pkg ∧
                          PkgSig bundle consumer pkg ∧ hsame h n)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier vTRefusal tHTransport hCConsumer refusalPkg transportPkg consumerPkg
  have sourceWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
        Cont v t refusalRead ∧ Cont t h transportRead ∧ Cont h c consumer ∧
          hsame consumer consumer :=
    ⟨carrier, vTRefusal, tHTransport, hCConsumer, hsame_refl consumer⟩
  obtain ⟨_eUnary, _aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    eAV, eTH, _hCN, pPkg, nPkg, hN⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer sourceWitness
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
        ⟨eAV, eTH, vTRefusal, tHTransport,
          cont_result_hsame_transport hCConsumer (hsame_symm source.right.right.right.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport consumerUnary (hsame_symm source.right.right.right.right), pPkg,
          nPkg, refusalPkg, transportPkg, consumerPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
