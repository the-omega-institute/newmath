import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealModulusFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealModulusFusionCarrier [AskSetup] [PackageSetup]
    (X M T W R S E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
  Prop :=
  UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
    UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory N ∧ Cont X M T ∧ Cont T W R ∧ Cont R S E ∧
        Cont H C N ∧ PkgSig bundle P pkg

theorem RealModulusFusionNamecertObligations [AskSetup] [PackageSetup]
    {X M T W R S E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row M ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
              hsame row S ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame ∧
        UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
          UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier
  obtain ⟨xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, _hUnary, _cUnary,
    nUnary, _sourceModulus, _tailWindow, _handoffSeal, _hContCName, pkgRow⟩ := carrier
  have sourceName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row M ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
              hsame row S ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceName
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
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgRow⟩
  }
  exact ⟨cert, xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary⟩

theorem RealModulusFusionRegseqHandoff [AskSetup] [PackageSetup]
    {X M T W R S E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg →
      Cont T W R ∧ Cont R S E ∧ UnaryHistory R ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  obtain ⟨_xUnary, _mUnary, _tUnary, _wUnary, rUnary, _sUnary, _eUnary, _hUnary, _cUnary,
    _nUnary, _sourceModulus, tailWindow, handoffSeal, _hContCName, pkgRow⟩ := carrier
  exact ⟨tailWindow, handoffSeal, rUnary, pkgRow⟩

theorem RealModulusFusionSharedTailWindowExhaustion [AskSetup] [PackageSetup]
    {X M T W R S E H C P N consumer : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      Cont W consumer R ->
        Cont E consumer N ->
          UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory R ∧
            UnaryHistory E ∧ Cont X M T ∧ Cont T W R ∧ Cont R S E ∧
              Cont W consumer R ∧ Cont E consumer N ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowConsumer sealConsumer
  obtain ⟨_xUnary, mUnary, tUnary, wUnary, rUnary, _sUnary, eUnary, _hUnary, _cUnary,
    _nUnary, sourceModulus, tailWindow, handoffSeal, _hContCName, pkgRow⟩ := carrier
  exact
    ⟨mUnary, tUnary, wUnary, rUnary, eUnary, sourceModulus, tailWindow, handoffSeal,
      windowConsumer, sealConsumer, pkgRow⟩

theorem RealModulusFusionRealSealBoundary [AskSetup] [PackageSetup]
    {X M T W R S E H C P N sealRow : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      Cont E N sealRow ->
        PkgSig bundle sealRow pkg ->
          UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
            UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory sealRow ∧
              Cont X M T ∧ Cont T W R ∧ Cont R S E ∧ Cont E N sealRow ∧
                PkgSig bundle sealRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier sealRoute sealPkg
  obtain ⟨xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, _hUnary, _cUnary,
    nUnary, sourceModulus, tailWindow, handoffSeal, _hContCName, _pkgRow⟩ := carrier
  have sealUnary : UnaryHistory sealRow := unary_cont_closed eUnary nUnary sealRoute
  exact
    ⟨xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, sealUnary,
      sourceModulus, tailWindow, handoffSeal, sealRoute, sealPkg⟩

theorem RealModulusFusionObligationEnvelope [AskSetup] [PackageSetup]
    {X M T W R S E H C P N consumer sealRow : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      Cont W consumer R ->
        Cont E consumer N ->
          Cont E N sealRow ->
            PkgSig bundle sealRow pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row N ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row M ∨ hsame row T ∨ hsame row W ∨
                      hsame row R ∨ hsame row S ∨ hsame row E ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row N)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
                  UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧ Cont X M T ∧
                    Cont T W R ∧ Cont R S E ∧ Cont W consumer R ∧ Cont E consumer N ∧
                      Cont E N sealRow ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle sealRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier windowConsumer sealConsumer sealRoute sealPkg
  obtain ⟨cert, xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary⟩ :=
    RealModulusFusionNamecertObligations carrier
  obtain ⟨_mWindow, _tWindow, _wWindow, _rWindow, _eWindow, sourceModulus, tailWindow,
    handoffSeal, windowConsumerRoute, sealConsumerRoute, pkgRow⟩ :=
      RealModulusFusionSharedTailWindowExhaustion carrier windowConsumer sealConsumer
  obtain ⟨_tailWindow, _handoffSeal, _rHandoff, _pkgHandoff⟩ :=
    RealModulusFusionRegseqHandoff carrier
  obtain ⟨_xSeal, _mSeal, _tSeal, _wSeal, _rSeal, _sSeal, _eSeal, _sealUnary,
    _sourceSeal, _tailSeal, _handoffSealRoute, sealRouteOut, sealPkgOut⟩ :=
      RealModulusFusionRealSealBoundary carrier sealRoute sealPkg
  exact
    ⟨cert, xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, sourceModulus,
      tailWindow, handoffSeal, windowConsumerRoute, sealConsumerRoute, sealRouteOut,
        pkgRow, sealPkgOut⟩

theorem RealModulusFusionNonescape [AskSetup] [PackageSetup]
    {X M T W R S E H C P N row : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      (hsame row X ∨ hsame row M ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
        hsame row S ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
          hsame row N) ->
        UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
          UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory H ∧
            UnaryHistory C ∧ UnaryHistory N ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory
  intro carrier visibleRow
  obtain ⟨xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, hUnary, cUnary,
    nUnary, _sourceModulus, _tailWindow, _handoffSeal, _hContCName, pkgRow⟩ := carrier
  have exposed :
      UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
        UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory H ∧
          UnaryHistory C ∧ UnaryHistory N ∧ PkgSig bundle P pkg :=
    ⟨xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, hUnary, cUnary, nUnary,
      pkgRow⟩
  cases visibleRow with
  | inl _sameX =>
      exact exposed
  | inr visibleTail =>
      cases visibleTail with
      | inl _sameM =>
          exact exposed
      | inr visibleTail =>
          cases visibleTail with
          | inl _sameT =>
              exact exposed
          | inr visibleTail =>
              cases visibleTail with
              | inl _sameW =>
                  exact exposed
              | inr visibleTail =>
                  cases visibleTail with
                  | inl _sameR =>
                      exact exposed
                  | inr visibleTail =>
                      cases visibleTail with
                      | inl _sameS =>
                          exact exposed
                      | inr visibleTail =>
                          cases visibleTail with
                          | inl _sameE =>
                              exact exposed
                          | inr visibleTail =>
                              cases visibleTail with
                              | inl _sameH =>
                                  exact exposed
                              | inr visibleTail =>
                                  cases visibleTail with
                                  | inl _sameC =>
                                      exact exposed
                                  | inr visibleTail =>
                                      cases visibleTail with
                                      | inl _sameP =>
                                          exact exposed
                                      | inr _sameN =>
                                          exact exposed

theorem RealModulusFusionSharedBudgetNormalization [AskSetup] [PackageSetup]
    {X M T W R S E H C P N budgetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      Cont M T W ->
        Cont W R budgetRead ->
          Cont budgetRead S sealRead ->
            PkgSig bundle P pkg ->
              UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory R ∧
                UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory budgetRead ∧
                  UnaryHistory sealRead ∧ Cont M T W ∧ Cont W R budgetRead ∧
                    Cont budgetRead S sealRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier modulusWindow budgetRoute sealRoute pkgRow
  obtain ⟨_xUnary, mUnary, tUnary, _wUnary, rUnary, sUnary, eUnary, _hUnary, _cUnary,
    _nUnary, _sourceModulus, _tailWindow, _handoffSeal, _hContCName, _carrierPkg⟩ :=
      carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed (unary_cont_closed mUnary tUnary modulusWindow) rUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetUnary sUnary sealRoute
  exact
    ⟨mUnary, tUnary, unary_cont_closed mUnary tUnary modulusWindow, rUnary, sUnary,
      eUnary, budgetUnary, sealUnary, modulusWindow, budgetRoute, sealRoute, pkgRow⟩

theorem RealModulusFusionL10ScopeRoute [AskSetup] [PackageSetup]
    {X M T W R S E H C P N budgetRead sealRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      Cont M T W ->
        Cont W R budgetRead ->
          Cont budgetRead S sealRead ->
            Cont E N realSeal ->
              PkgSig bundle P pkg ->
                PkgSig bundle realSeal pkg ->
                  UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
                    UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧
                      UnaryHistory budgetRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory realSeal ∧ Cont X M T ∧ Cont M T W ∧
                          Cont W R budgetRead ∧ Cont budgetRead S sealRead ∧
                            Cont E N realSeal ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier modulusWindow budgetRoute sealRoute realSealRoute pkgRow realSealPkg
  obtain ⟨xUnary, mUnary, tUnary, _wUnary, rUnary, sUnary, eUnary, _hUnary, _cUnary,
    nUnary, sourceModulus, _tailWindow, _handoffSeal, _hContCName, _carrierPkg⟩ :=
      carrier
  have wBudgetUnary : UnaryHistory W :=
    unary_cont_closed mUnary tUnary modulusWindow
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed wBudgetUnary rUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetUnary sUnary sealRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed eUnary nUnary realSealRoute
  exact
    ⟨xUnary, mUnary, tUnary, wBudgetUnary, rUnary, sUnary, eUnary, budgetUnary,
      sealUnary, realSealUnary, sourceModulus, modulusWindow, budgetRoute, sealRoute,
        realSealRoute, pkgRow, realSealPkg⟩

theorem RealModulusFusionObligationClosure [AskSetup] [PackageSetup]
    {X M T W R S E H C P N budgetRead sealRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      Cont M T W ->
        Cont W R budgetRead ->
          Cont budgetRead S sealRead ->
            Cont E N realSeal ->
              PkgSig bundle P pkg ->
                PkgSig bundle realSeal pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row N ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row M ∨ hsame row T ∨ hsame row W ∨
                          hsame row R ∨ hsame row S ∨ hsame row E ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
                      hsame ∧
                    UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
                      UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧
                        UnaryHistory budgetRead ∧ UnaryHistory sealRead ∧
                          UnaryHistory realSeal ∧ Cont X M T ∧ Cont M T W ∧
                            Cont W R budgetRead ∧ Cont budgetRead S sealRead ∧
                              Cont E N realSeal ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier modulusWindow budgetRoute sealRoute realSealRoute pkgRow realSealPkg
  obtain ⟨cert, _xName, _mName, _tName, _wName, _rName, _sName, _eName⟩ :=
    RealModulusFusionNamecertObligations carrier
  obtain ⟨xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, budgetUnary,
    sealUnary, realSealUnary, sourceModulus, modulusWindowOut, budgetRouteOut,
      sealRouteOut, realSealRouteOut, pkgRowOut, realSealPkgOut⟩ :=
        RealModulusFusionL10ScopeRoute carrier modulusWindow budgetRoute sealRoute
          realSealRoute pkgRow realSealPkg
  exact
    ⟨cert, xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, budgetUnary,
      sealUnary, realSealUnary, sourceModulus, modulusWindowOut, budgetRouteOut,
        sealRouteOut, realSealRouteOut, pkgRowOut, realSealPkgOut⟩

end BEDC.Derived.RealModulusFusionUp
