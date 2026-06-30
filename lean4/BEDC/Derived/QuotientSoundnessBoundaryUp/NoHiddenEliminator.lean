import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_no_hidden_eliminator [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle consumer pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row refusalRead ∨ hsame row transportRead ∨
                          hsame row consumer)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle consumer pkg ∧
                          PkgSig bundle p pkg)
                      hsame ∧
                    UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier _vTRefusal _tHTransport hCConsumer _refusalPkg _transportPkg consumerPkg
  obtain ⟨_eUnary, _aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, _eTH, _hCN, pPkg, _nPkg, _hN⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row refusalRead ∨ hsame row transportRead ∨ hsame row consumer)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle consumer pkg ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer
          (And.intro (hsame_refl consumer) consumerUnary)
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
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact And.intro source.right (And.intro consumerPkg pPkg)
    }
  exact And.intro cert consumerUnary

end BEDC.Derived.QuotientSoundnessBoundaryUp
