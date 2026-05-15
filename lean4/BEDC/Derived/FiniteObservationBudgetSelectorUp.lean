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

theorem FiniteObservationBudgetSelectorCarrier_tail_meet_seal_compatibility
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N tailMeetRead limitSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E tailMeetRead ->
        Cont R E limitSealRead ->
          PkgSig bundle tailMeetRead pkg ->
            PkgSig bundle limitSealRead pkg ->
              UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧
                UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory tailMeetRead ∧
                  UnaryHistory limitSealRead ∧ Cont B S W ∧ Cont W D R ∧
                    Cont R E tailMeetRead ∧ Cont R E limitSealRead ∧
                      hsame tailMeetRead limitSealRead ∧
                        PkgSig bundle tailMeetRead pkg ∧
                          PkgSig bundle limitSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier tailMeetSeal limitSeal tailMeetPkg limitSealPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, budgetSchedule, windowDyadic,
    _regularSeal, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetSchedule
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowDyadic
  have unaryTailMeet : UnaryHistory tailMeetRead :=
    unary_cont_closed unaryR unaryE tailMeetSeal
  have unaryLimitSeal : UnaryHistory limitSealRead :=
    unary_cont_closed unaryR unaryE limitSeal
  have sameReads : hsame tailMeetRead limitSealRead :=
    cont_deterministic tailMeetSeal limitSeal
  exact
    ⟨unaryB, unaryS, unaryW, unaryD, unaryR, unaryE, unaryTailMeet, unaryLimitSeal,
      budgetSchedule, windowDyadic, tailMeetSeal, limitSeal, sameReads, tailMeetPkg,
      limitSealPkg⟩

theorem FiniteObservationBudgetSelectorCarrier_dyadic_window_exhaustion
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont W D dyadicRead ->
        PkgSig bundle dyadicRead pkg ->
          UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory dyadicRead ∧
            Cont W D dyadicRead ∧ hsame R dyadicRead ∧
              PkgSig bundle dyadicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier windowDyadicRead dyadicPkg
  obtain ⟨unaryB, unaryS, unaryD, _unaryE, budgetSchedule, windowDyadic,
    _regularSeal, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetSchedule
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowDyadic
  have unaryDyadicRead : UnaryHistory dyadicRead :=
    unary_cont_closed unaryW unaryD windowDyadicRead
  have sameRead : hsame R dyadicRead :=
    cont_respects_hsame (hsame_refl W) (hsame_refl D) windowDyadic windowDyadicRead
  exact ⟨unaryW, unaryD, unaryDyadicRead, windowDyadicRead, sameRead, dyadicPkg⟩

theorem FiniteObservationBudgetSelectorCarrier_budget_choice_freeness
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N budgetRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont B S budgetRead ->
        Cont budgetRead D windowRead ->
          Cont windowRead E sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
                UnaryHistory budgetRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory sealRead ∧ Cont B S budgetRead ∧
                    Cont budgetRead D windowRead ∧ Cont windowRead E sealRead ∧
                      hsame W budgetRead ∧ hsame R windowRead ∧ hsame C sealRead ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier budgetRoute windowRoute sealRoute sealPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, carrierBudget, carrierWindow, carrierSeal,
    _sameName⟩ := carrier
  have unaryBudgetRead : UnaryHistory budgetRead :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryWindowRead : UnaryHistory windowRead :=
    unary_cont_closed unaryBudgetRead unaryD windowRoute
  have unarySealRead : UnaryHistory sealRead :=
    unary_cont_closed unaryWindowRead unaryE sealRoute
  have sameBudget : hsame W budgetRead :=
    cont_respects_hsame (hsame_refl B) (hsame_refl S) carrierBudget budgetRoute
  have sameWindow : hsame R windowRead :=
    cont_respects_hsame sameBudget (hsame_refl D) carrierWindow windowRoute
  have sameSeal : hsame C sealRead :=
    cont_respects_hsame sameWindow (hsame_refl E) carrierSeal sealRoute
  exact
    ⟨unaryB, unaryS, unaryD, unaryE, unaryBudgetRead, unaryWindowRead, unarySealRead,
      budgetRoute, windowRoute, sealRoute, sameBudget, sameWindow, sameSeal, sealPkg⟩

theorem FiniteObservationBudgetSelectorCarrier_window_seal_commutation
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N windowFirst routeFirst sealFirst : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont W E windowFirst ->
        Cont B E routeFirst ->
          Cont W E sealFirst ->
            PkgSig bundle windowFirst pkg ->
              PkgSig bundle routeFirst pkg ->
                hsame windowFirst sealFirst ∧ UnaryHistory windowFirst ∧
                  UnaryHistory routeFirst ∧ Cont W E windowFirst ∧ Cont B E routeFirst ∧
                    PkgSig bundle windowFirst pkg ∧
                      PkgSig bundle routeFirst pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier windowRoute routeRoute sealRoute windowPkg routePkg
  obtain ⟨unaryB, unaryS, _unaryD, unaryE, budgetSchedule, _windowDyadic,
    _regularSeal, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetSchedule
  have windowUnary : UnaryHistory windowFirst :=
    unary_cont_closed unaryW unaryE windowRoute
  have routeUnary : UnaryHistory routeFirst :=
    unary_cont_closed unaryB unaryE routeRoute
  have sameWindowSeal : hsame windowFirst sealFirst :=
    cont_deterministic windowRoute sealRoute
  exact
    ⟨sameWindowSeal, windowUnary, routeUnary, windowRoute, routeRoute, windowPkg, routePkg⟩

theorem FiniteObservationBudgetSelectorCarrier_diagonal_consumer_boundary
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E diagonalRead ->
        PkgSig bundle diagonalRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
                hsame row diagonalRead)
            (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
            (fun row : BHist =>
              PkgSig bundle diagonalRead pkg ∧ hsame row diagonalRead ∧
                Cont B S W ∧ Cont W D R)
            hsame ∧ Cont B S W ∧ Cont W D R ∧ Cont R E diagonalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier diagonalRoute diagonalPkg
  have carrierWitness := carrier
  obtain ⟨unaryB, unaryS, unaryD, unaryE, routeW, routeR, _routeC, _sameName⟩ :=
    carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryDiagonalRead : UnaryHistory diagonalRead :=
    unary_cont_closed unaryR unaryE diagonalRoute
  have sourceDiagonal :
      (fun row : BHist =>
        FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
          hsame row diagonalRead) diagonalRead := by
    exact And.intro carrierWitness (hsame_refl diagonalRead)
  have core :
      NameCert
        (fun row : BHist =>
          FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
            hsame row diagonalRead)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro diagonalRead sourceDiagonal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowDiagonal : hsame row diagonalRead := sourceRow.right
        have sameOtherDiagonal : hsame other diagonalRead :=
          hsame_trans (hsame_symm same) sameRowDiagonal
        exact And.intro sourceRow.left sameOtherDiagonal
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
            hsame row diagonalRead)
        (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          PkgSig bundle diagonalRead pkg ∧ hsame row diagonalRead ∧
            Cont B S W ∧ Cont W D R)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport unaryDiagonalRead (hsame_symm sourceRow.right)
        exact And.intro sourceRow.right rowUnary
      ledger_sound := by
        intro row sourceRow
        exact ⟨diagonalPkg, sourceRow.right, routeW, routeR⟩
    }
  exact ⟨cert, routeW, routeR, diagonalRoute⟩

theorem FiniteObservationBudgetSelectorCarrier_nonescape
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E sealRead →
        PkgSig bundle sealRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ∧
                hsame row sealRead)
            (fun _row : BHist =>
              Cont B S W ∧ Cont W D R ∧ Cont R E sealRead ∧ hsame N E)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sealRoute sealPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, budgetSchedule, windowDyadic,
    regularSeal, sameEndpoint⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetSchedule
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowDyadic
  have unarySealRead : UnaryHistory sealRead :=
    unary_cont_closed unaryR unaryE sealRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead (And.intro
          ⟨unaryB, unaryS, unaryD, unaryE, budgetSchedule, windowDyadic, regularSeal,
            sameEndpoint⟩
          (hsame_refl sealRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨budgetSchedule, windowDyadic, sealRoute, sameEndpoint⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport unarySealRead (hsame_symm source.right), sealPkg⟩
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp
