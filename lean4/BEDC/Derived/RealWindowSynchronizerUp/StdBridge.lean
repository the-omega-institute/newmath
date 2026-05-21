import BEDC.Derived.RealWindowSynchronizerUp.BudgetPullback
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealWindowSynchronizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowSynchronizerUp_StdBridge [AskSetup] [PackageSetup]
    {W R T L S H C P N limitRead realRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowSynchronizerCarrier W R T L S H C P N →
      Cont T L limitRead →
        Cont limitRead S realRead →
          Cont realRead N bridgeRead →
            PkgSig bundle bridgeRead pkg →
              UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory L ∧
                UnaryHistory S ∧ UnaryHistory N ∧ UnaryHistory limitRead ∧
                  UnaryHistory realRead ∧ UnaryHistory bridgeRead ∧ Cont W R T ∧
                    Cont T L limitRead ∧ Cont limitRead S realRead ∧
                      Cont realRead N bridgeRead ∧ hsame N S ∧
                        PkgSig bundle bridgeRead pkg ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                            (fun row : BHist => Cont realRead N row ∧ Cont T L limitRead)
                            (fun row : BHist => hsame row bridgeRead ∧
                              PkgSig bundle bridgeRead pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier limitRoute realRoute bridgeRoute pkgBridge
  obtain ⟨unaryW, unaryR, unaryT, unaryL, unaryS, _unaryH, _unaryC, _unaryP,
    unaryN, windowRoute, sameNS⟩ := carrier
  have unaryLimit : UnaryHistory limitRead :=
    unary_cont_closed unaryT unaryL limitRoute
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unaryLimit unaryS realRoute
  have unaryBridge : UnaryHistory bridgeRead :=
    unary_cont_closed unaryReal unaryN bridgeRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
        (fun row : BHist => Cont realRead N row ∧ Cont T L limitRead)
        (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, unaryBridge⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport bridgeRoute (hsame_symm source.left),
          limitRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgBridge⟩
  }
  exact
    ⟨unaryW, unaryR, unaryT, unaryL, unaryS, unaryN, unaryLimit, unaryReal,
      unaryBridge, windowRoute, limitRoute, realRoute, bridgeRoute, sameNS, pkgBridge,
      cert⟩

end BEDC.Derived.RealWindowSynchronizerUp
