import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_downstream_factorization_exactness
    [AskSetup] [PackageSetup]
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
                        PkgSig bundle refusalRead pkg ∧
                          PkgSig bundle transportRead pkg ∧
                            PkgSig bundle consumer pkg ∧ hsame row consumer)
                      hsame ∧
                    UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                      UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier vTRefusal tHTransport hCConsumer refusalPkg transportPkg consumerPkg
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, _eTH, _hCN, _pPkg, _nPkg, _hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalRead ∨ hsame row transportRead ∨ hsame row consumer)
          (fun row : BHist =>
            PkgSig bundle refusalRead pkg ∧ PkgSig bundle transportRead pkg ∧
              PkgSig bundle consumer pkg ∧ hsame row consumer)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨refusalPkg, transportPkg, consumerPkg, source.left⟩
  }
  exact ⟨cert, refusalUnary, transportUnary, consumerUnary⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
