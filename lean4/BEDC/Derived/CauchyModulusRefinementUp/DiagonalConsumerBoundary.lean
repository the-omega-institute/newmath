import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_diagonal_consumer_boundary [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead diagonalRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h diagonalRead ->
              Cont diagonalRead c consumerRead ->
                PkgSig bundle consumerRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                          bundle pkg ∧
                        hsame row consumerRead)
                    (fun row : BHist =>
                      Cont m0 m1 u ∧ Cont u v t ∧ Cont t w selected ∧
                        Cont selected q readback ∧ Cont readback e sealRead ∧
                          Cont sealRead h diagonalRead ∧ Cont diagonalRead c row ∧
                            PkgSig bundle consumerRead pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumerRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier tWSelected selectedQReadback readbackESeal sealHDiagonal
    diagonalCConsumer consumerPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed sealReadUnary hUnary sealHDiagonal
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed diagonalReadUnary cUnary diagonalCConsumer
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl consumerRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨m0m1u, uvt, tWSelected, selectedQReadback, readbackESeal, sealHDiagonal,
          cont_result_hsame_transport diagonalCConsumer (hsame_symm source.right),
          consumerPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport consumerReadUnary (hsame_symm source.right), consumerPkg⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
