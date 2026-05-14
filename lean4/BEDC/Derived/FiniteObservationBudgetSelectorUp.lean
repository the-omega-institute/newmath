import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteObservationBudgetSelectorCarrier (B S W D R E _H C _P N : BHist) : Prop :=
  UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
    Cont B S W ∧ Cont W D R ∧ Cont R E C ∧ hsame N E

theorem FiniteObservationBudgetSelectorCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      PkgSig bundle E pkg ->
        UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
          UnaryHistory R ∧ UnaryHistory E ∧ Cont B S W ∧ Cont W D R ∧ Cont R E C ∧
            hsame N E ∧
              SemanticNameCert
                (fun row : BHist => hsame row E ∧ UnaryHistory row)
                (fun row : BHist => hsame row E)
                (fun row : BHist => hsame row E ∧ PkgSig bundle E pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier pkgSig
  obtain ⟨unaryB, unaryS, unaryD, unaryE, routeW, routeR, routeC, sameEndpoint⟩ :=
    carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have sourceE : (fun row : BHist => hsame row E ∧ UnaryHistory row) E := by
    exact And.intro (hsame_refl E) unaryE
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row E ∧ UnaryHistory row)
        (fun row : BHist => hsame row E)
        (fun row : BHist => hsame row E ∧ PkgSig bundle E pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro E sourceE
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
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pkgSig
    }
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, routeW, routeR, routeC,
      sameEndpoint, cert⟩

theorem FiniteObservationBudgetSelectorCarrier_schedule_admission
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      PkgSig bundle W pkg →
        UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ Cont B S W ∧
          SemanticNameCert
            (fun row : BHist => hsame row W ∧ UnaryHistory row)
            (fun row : BHist => hsame row W)
            (fun row : BHist => hsame row W ∧ PkgSig bundle W pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier pkgSig
  obtain ⟨unaryB, unaryS, _unaryD, _unaryE, routeW, _routeR, _routeC,
    _sameEndpoint⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have sourceW : (fun row : BHist => hsame row W ∧ UnaryHistory row) W := by
    exact And.intro (hsame_refl W) unaryW
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row W ∧ UnaryHistory row)
        (fun row : BHist => hsame row W)
        (fun row : BHist => hsame row W ∧ PkgSig bundle W pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro W sourceW
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
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pkgSig
    }
  exact ⟨unaryB, unaryS, unaryW, routeW, cert⟩

theorem FiniteObservationBudgetSelectorCarrier_budget_route_determinacy
    [AskSetup] (_ps : PackageSetup)
    {B S W D R E H C P N W' R' C' : BHist} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont B S W' ->
        Cont W' D R' ->
          Cont R' E C' ->
            hsame W W' ∧ hsame R R' ∧ hsame C C' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier budgetSchedule' windowDyadic' regularSeal'
  obtain ⟨_unaryB, _unaryS, _unaryD, _unaryE, budgetSchedule, windowDyadic,
    regularSeal, _sameName⟩ := carrier
  have sameWindow : hsame W W' :=
    cont_respects_hsame (hsame_refl B) (hsame_refl S) budgetSchedule budgetSchedule'
  have sameRegular : hsame R R' :=
    cont_respects_hsame sameWindow (hsame_refl D) windowDyadic windowDyadic'
  have sameSeal : hsame C C' :=
    cont_respects_hsame sameRegular (hsame_refl E) regularSeal regularSeal'
  exact ⟨sameWindow, sameRegular, sameSeal⟩

theorem FiniteObservationBudgetSelectorCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {B S W D R E H C P N realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E realRead →
        PkgSig bundle realRead pkg →
          UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
            UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory realRead ∧ Cont B S W ∧
              Cont W D R ∧ Cont R E realRead ∧ hsame N E ∧
                PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier realSeal realReadPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, routeW, routeR, _routeC, sameName⟩ :=
    carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryRealRead : UnaryHistory realRead :=
    unary_cont_closed unaryR unaryE realSeal
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryRealRead, routeW, routeR,
      realSeal, sameName, realReadPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
