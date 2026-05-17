import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_four_face_consumer_boundary [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              Cont publicRead c consumer ->
                PkgSig bundle consumer pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                        hsame row consumer)
                    (fun row : BHist =>
                      Cont t w selected ∧ Cont selected q readback ∧ Cont readback e sealRead ∧
                        Cont sealRead h publicRead ∧ Cont publicRead c row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle consumer pkg ∧ hsame h n)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic publicCConsumer
    consumerPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  let carrierPacket :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealHPublic
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed publicReadUnary cUnary publicCConsumer
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer (And.intro carrierPacket (hsame_refl consumer))
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
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨tWSelected, selectedQReadback, readbackESeal, sealHPublic,
          cont_result_hsame_transport publicCConsumer (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport consumerUnary (hsame_symm source.right), consumerPkg, hn⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
