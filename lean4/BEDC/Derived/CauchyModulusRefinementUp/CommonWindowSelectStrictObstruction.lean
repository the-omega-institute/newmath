import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCommonWindowSelectStrictObstruction
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead obstruction
      terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              Cont publicRead n obstruction ->
                Cont obstruction c terminal ->
                  PkgSig bundle terminal pkg ->
                    SemanticNameCert
                      (fun row : BHist =>
                        CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                          bundle pkg ∧ hsame row terminal)
                      (fun row : BHist =>
                        Cont t w selected ∧ Cont selected q readback ∧
                          Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                            Cont publicRead n obstruction ∧ Cont obstruction c row)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminal pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier selectedRoute readbackRoute sealRoute publicRoute obstructionRoute
    terminalRoute terminalPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have carrierPacket :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary publicRoute
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed publicUnary nUnary obstructionRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed obstructionUnary cUnary terminalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminal ⟨carrierPacket, hsame_refl terminal⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨selectedRoute, readbackRoute, sealRoute, publicRoute, obstructionRoute,
          cont_result_hsame_transport terminalRoute (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport terminalUnary (hsame_symm source.right), terminalPkg⟩
  }

theorem CauchyModulusRefinementCarrier_common_window_select_strict_obstruction
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w q ->
        Cont q e h ->
          Cont h c refusalRead ->
            PkgSig bundle refusalRead pkg ->
              UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory h ∧
                UnaryHistory refusalRead ∧ Cont t w q ∧ Cont q e h ∧
                  Cont h c refusalRead ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier windowRoute sealRoute refusalRoute refusalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, _qUnary, eUnary,
      hUnary, cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have qUnary : UnaryHistory q :=
    unary_cont_closed tUnary wUnary windowRoute
  have hUnaryFromSeal : UnaryHistory h :=
    unary_cont_closed qUnary eUnary sealRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed hUnary cUnary refusalRoute
  exact
    ⟨wUnary, qUnary, eUnary, hUnaryFromSeal, refusalUnary, windowRoute, sealRoute,
      refusalRoute, pPkg, refusalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
