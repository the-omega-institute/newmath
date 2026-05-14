import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalTailSelectorCarrier [AskSetup] [PackageSetup]
    (r n mu k w d t s h c p name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory r ∧ UnaryHistory n ∧ UnaryHistory mu ∧ UnaryHistory k ∧
    UnaryHistory w ∧ UnaryHistory d ∧ UnaryHistory t ∧ UnaryHistory s ∧
      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory name ∧
        Cont n mu k ∧ Cont k w d ∧ PkgSig bundle p pkg

def DiagonalTailSelectorPublicBudgetSource [AskSetup] [PackageSetup]
    (r n mu k w d t s h c p name publicRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg ∧
    Cont p name publicRow ∧ PkgSig bundle publicRow pkg

theorem DiagonalTailSelectorCarrier_window_choice_totality [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg →
      Cont h c sourceRead →
      PkgSig bundle sourceRead pkg →
        UnaryHistory n ∧ UnaryHistory mu ∧ UnaryHistory k ∧ UnaryHistory w ∧
          UnaryHistory d ∧ UnaryHistory sourceRead ∧ Cont n mu k ∧ Cont k w d ∧
            Cont h c sourceRead ∧ PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier sourceRoute sourcePkg
  obtain ⟨_rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, _tUnary, _sUnary,
    hUnary, cUnary, _pUnary, _nameUnary, nmuRoute, kwRoute, _pPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed hUnary cUnary sourceRoute
  exact
    ⟨nUnary, muUnary, kUnary, wUnary, dUnary, sourceUnary, nmuRoute, kwRoute,
      sourceRoute, sourcePkg⟩

theorem DiagonalTailSelectorCarrier_window_threshold_order [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg →
      Cont w d t →
      Cont t s tailRead →
      Cont tailRead s sealRead →
      PkgSig bundle sealRead pkg →
        UnaryHistory n ∧ UnaryHistory mu ∧ UnaryHistory k ∧ UnaryHistory w ∧
          UnaryHistory d ∧ UnaryHistory t ∧ UnaryHistory s ∧ UnaryHistory tailRead ∧
            UnaryHistory sealRead ∧ Cont n mu k ∧ Cont k w d ∧ Cont w d t ∧
              Cont t s tailRead ∧ Cont tailRead s sealRead ∧ PkgSig bundle p pkg ∧
                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier wdRoute tailRoute sealRoute sealPkg
  obtain ⟨_rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary,
    _hUnary, _cUnary, _pUnary, _nameUnary, nMuK, kWD, pPkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed tUnary sUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  exact
    ⟨nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary, tailUnary,
      sealUnary, nMuK, kWD, wdRoute, tailRoute, sealRoute, pPkg, sealPkg⟩

theorem DiagonalTailSelectorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg →
      Cont w d t →
      Cont t s consumer →
      PkgSig bundle consumer pkg →
        UnaryHistory r ∧ UnaryHistory n ∧ UnaryHistory mu ∧ UnaryHistory k ∧
          UnaryHistory w ∧ UnaryHistory d ∧ UnaryHistory t ∧ UnaryHistory s ∧
            UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory name ∧
              UnaryHistory consumer ∧ Cont n mu k ∧ Cont k w d ∧ Cont w d t ∧
                Cont t s consumer ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle consumer pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row p ∧ UnaryHistory row)
                      (fun row : BHist => hsame row p)
                      (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier wdRoute consumerRoute consumerPkg
  obtain ⟨rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary,
    hUnary, cUnary, pUnary, nameUnary, nmuRoute, kwRoute, pPkg⟩ := carrier
  have tUnaryFromRoute : UnaryHistory t :=
    unary_cont_closed wUnary dUnary wdRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tUnaryFromRoute sUnary consumerRoute
  have sourceP : (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact And.intro (hsame_refl p) pUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro p sourceP
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
        exact And.intro source.left pPkg
    }
  exact
    ⟨rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary, hUnary,
      cUnary, pUnary, nameUnary, consumerUnary, nmuRoute, kwRoute, wdRoute,
      consumerRoute, pPkg, consumerPkg, cert⟩

theorem DiagonalTailSelectorCarrier_public_budget_export [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name consumer publicRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg →
      Cont w d t →
      Cont t s consumer →
      Cont p name publicRow →
      PkgSig bundle consumer pkg →
      PkgSig bundle publicRow pkg →
        UnaryHistory publicRow ∧ Cont p name publicRow ∧ PkgSig bundle publicRow pkg ∧
          SemanticNameCert
            (fun row : BHist => hsame row p ∧ UnaryHistory row)
            (fun row : BHist => hsame row p)
            (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier _wdRoute _consumerRoute publicRoute _consumerPkg publicPkg
  obtain ⟨_rUnary, _nUnary, _muUnary, _kUnary, _wUnary, _dUnary, _tUnary, _sUnary,
    _hUnary, _cUnary, pUnary, nameUnary, _nmuRoute, _kwRoute, pPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed pUnary nameUnary publicRoute
  have sourceP : (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact And.intro (hsame_refl p) pUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro p sourceP
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
        exact And.intro source.left pPkg
    }
  exact ⟨publicUnary, publicRoute, publicPkg, cert⟩

theorem DiagonalTailSelectorPublicBudgetSource_tail_budget_compatibility
    [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name publicRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorPublicBudgetSource r n mu k w d t s h c p name publicRow
      bundle pkg ->
      Cont w d t ->
      Cont t s consumer ->
      PkgSig bundle consumer pkg ->
        UnaryHistory publicRow ∧ UnaryHistory consumer ∧ Cont w d t ∧
          Cont t s consumer ∧ Cont p name publicRow ∧ PkgSig bundle consumer pkg ∧
            PkgSig bundle publicRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro source wdRoute consumerRoute consumerPkg
  obtain ⟨carrier, publicRoute, publicPkg⟩ := source
  obtain ⟨_rUnary, _nUnary, _muUnary, _kUnary, wUnary, dUnary, _tUnary, sUnary,
    _hUnary, _cUnary, pUnary, nameUnary, _nmuRoute, _kwRoute, _pPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed pUnary nameUnary publicRoute
  have tUnaryFromRoute : UnaryHistory t :=
    unary_cont_closed wUnary dUnary wdRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tUnaryFromRoute sUnary consumerRoute
  exact
    ⟨publicUnary, consumerUnary, wdRoute, consumerRoute, publicRoute, consumerPkg,
      publicPkg⟩

theorem DiagonalTailSelectorCarrier_real_seal_boundary_scope [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name consumer publicRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg →
      Cont w d t →
      Cont t s consumer →
      Cont p name publicRow →
      PkgSig bundle consumer pkg →
      PkgSig bundle publicRow pkg →
        UnaryHistory s ∧ UnaryHistory consumer ∧ UnaryHistory publicRow ∧ Cont w d t ∧
          Cont t s consumer ∧ Cont p name publicRow ∧ PkgSig bundle consumer pkg ∧
            PkgSig bundle publicRow pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row p ∧ UnaryHistory row)
                (fun row : BHist => hsame row p)
                (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier wdRoute consumerRoute publicRoute consumerPkg publicPkg
  obtain ⟨_rUnary, _nUnary, _muUnary, _kUnary, wUnary, dUnary, _tUnary, sUnary,
    _hUnary, _cUnary, pUnary, nameUnary, _nmuRoute, _kwRoute, pPkg⟩ := carrier
  have tUnaryFromRoute : UnaryHistory t :=
    unary_cont_closed wUnary dUnary wdRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tUnaryFromRoute sUnary consumerRoute
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed pUnary nameUnary publicRoute
  have sourceP : (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact And.intro (hsame_refl p) pUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro p sourceP
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
        exact And.intro source.left pPkg
    }
  exact
    ⟨sUnary, consumerUnary, publicUnary, wdRoute, consumerRoute, publicRoute,
      consumerPkg, publicPkg, cert⟩

theorem DiagonalTailSelectorCarrier_tail_cofinality_factorization [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name schedulePrecision scheduleWindow scheduleDyadic
      scheduleRegseq scheduleSeal consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg →
      Cont schedulePrecision scheduleWindow scheduleDyadic →
      Cont scheduleDyadic scheduleRegseq scheduleSeal →
      hsame scheduleSeal s →
      Cont w d t →
      Cont t s consumer →
      PkgSig bundle consumer pkg →
        UnaryHistory scheduleDyadic ∧ UnaryHistory scheduleSeal ∧ UnaryHistory consumer ∧
          hsame scheduleSeal s ∧ Cont w d t ∧ Cont t s consumer ∧
            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier _scheduleWindowRoute scheduleSealRoute sameScheduleSeal wdRoute
    consumerRoute consumerPkg
  obtain ⟨_rUnary, _nUnary, _muUnary, _kUnary, wUnary, dUnary, tUnary, sUnary,
    _hUnary, _cUnary, _pUnary, _nameUnary, _nmuRoute, _kwRoute, _pPkg⟩ := carrier
  have scheduleSealUnary : UnaryHistory scheduleSeal :=
    unary_transport_symm sUnary sameScheduleSeal
  have scheduleDyadicUnary : UnaryHistory scheduleDyadic :=
    unary_cont_left_factor scheduleSealRoute scheduleSealUnary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tUnary sUnary consumerRoute
  exact ⟨scheduleDyadicUnary, scheduleSealUnary, consumerUnary, sameScheduleSeal,
    wdRoute, consumerRoute, consumerPkg⟩

theorem DiagonalTailSelectorCarrier_root_cofinal_admission [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name admissionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg ->
      Cont p name admissionRead ->
        PkgSig bundle p pkg ->
          UnaryHistory r ∧ UnaryHistory n ∧ UnaryHistory mu ∧ UnaryHistory k ∧
            UnaryHistory w ∧ UnaryHistory d ∧ UnaryHistory t ∧ UnaryHistory s ∧
              UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory name ∧
                UnaryHistory admissionRead ∧ Cont n mu k ∧ Cont k w d ∧
                  Cont p name admissionRead ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier pNameAdmission _pPkg
  obtain ⟨rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary,
    hUnary, cUnary, pUnary, nameUnary, nMuK, kWD, carrierPkg⟩ := carrier
  have admissionUnary : UnaryHistory admissionRead :=
    unary_cont_closed pUnary nameUnary pNameAdmission
  exact
    ⟨rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary, hUnary,
      cUnary, pUnary, nameUnary, admissionUnary, nMuK, kWD, pNameAdmission,
      carrierPkg⟩

theorem DiagonalTailSelectorCarrier_cofinal_budget_replay [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name admissionRead consumer replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg ->
      Cont p name admissionRead ->
        Cont w d t ->
          Cont t s consumer ->
            Cont consumer admissionRead replay ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle replay pkg ->
                  UnaryHistory r ∧ UnaryHistory n ∧ UnaryHistory mu ∧ UnaryHistory k ∧
                    UnaryHistory w ∧ UnaryHistory d ∧ UnaryHistory t ∧ UnaryHistory s ∧
                      UnaryHistory admissionRead ∧ UnaryHistory consumer ∧
                        UnaryHistory replay ∧ Cont n mu k ∧ Cont k w d ∧
                          Cont p name admissionRead ∧ Cont w d t ∧
                            Cont t s consumer ∧ Cont consumer admissionRead replay ∧
                              PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg ∧
                                PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier pNameAdmission wDT tSConsumer consumerAdmissionReplay consumerPkg replayPkg
  obtain ⟨rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, _tUnary, sUnary,
    _hUnary, _cUnary, pUnary, nameUnary, nMuK, kWD, pPkg⟩ := carrier
  have admissionUnary : UnaryHistory admissionRead :=
    unary_cont_closed pUnary nameUnary pNameAdmission
  have tUnaryFromRoute : UnaryHistory t :=
    unary_cont_closed wUnary dUnary wDT
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tUnaryFromRoute sUnary tSConsumer
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed consumerUnary admissionUnary consumerAdmissionReplay
  exact
    ⟨rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, tUnaryFromRoute, sUnary,
      admissionUnary, consumerUnary, replayUnary, nMuK, kWD, pNameAdmission, wDT,
      tSConsumer, consumerAdmissionReplay, pPkg, consumerPkg, replayPkg⟩

theorem DiagonalTailSelectorRootBudgetHandoff [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name budgetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorCarrier r n mu k w d t s h c p name bundle pkg →
      Cont d t budgetRead →
      Cont budgetRead s sealRead →
      PkgSig bundle sealRead pkg →
        UnaryHistory n ∧ UnaryHistory mu ∧ UnaryHistory k ∧ UnaryHistory w ∧
          UnaryHistory d ∧ UnaryHistory t ∧ UnaryHistory s ∧ UnaryHistory budgetRead ∧
            UnaryHistory sealRead ∧ Cont n mu k ∧ Cont k w d ∧
              Cont d t budgetRead ∧ Cont budgetRead s sealRead ∧ PkgSig bundle p pkg ∧
                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier budgetRoute sealRoute sealPkg
  obtain ⟨_rUnary, nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary,
    _hUnary, _cUnary, _pUnary, _nameUnary, nMuK, kWD, pPkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed dUnary tUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetUnary sUnary sealRoute
  exact
    ⟨nUnary, muUnary, kUnary, wUnary, dUnary, tUnary, sUnary, budgetUnary,
      sealUnary, nMuK, kWD, budgetRoute, sealRoute, pPkg, sealPkg⟩

theorem DiagonalTailSelectorCarrier_real_seal_budget_nonescape [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name publicRow consumer downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorPublicBudgetSource r n mu k w d t s h c p name publicRow
        bundle pkg →
      Cont w d t →
      Cont t s consumer →
      Cont publicRow consumer downstreamRead →
      PkgSig bundle consumer pkg →
      PkgSig bundle downstreamRead pkg →
        UnaryHistory publicRow ∧ UnaryHistory consumer ∧ UnaryHistory downstreamRead ∧
          Cont w d t ∧ Cont t s consumer ∧ Cont publicRow consumer downstreamRead ∧
            PkgSig bundle publicRow pkg ∧ PkgSig bundle consumer pkg ∧
              PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro source wdRoute consumerRoute downstreamRoute consumerPkg downstreamPkg
  obtain ⟨carrier, publicRoute, publicPkg⟩ := source
  obtain ⟨_rUnary, _nUnary, _muUnary, _kUnary, wUnary, dUnary, _tUnary, sUnary,
    _hUnary, _cUnary, pUnary, nameUnary, _nmuRoute, _kwRoute, _pPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed pUnary nameUnary publicRoute
  have tUnaryFromRoute : UnaryHistory t :=
    unary_cont_closed wUnary dUnary wdRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tUnaryFromRoute sUnary consumerRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed publicUnary consumerUnary downstreamRoute
  exact
    ⟨publicUnary, consumerUnary, downstreamUnary, wdRoute, consumerRoute,
      downstreamRoute, publicPkg, consumerPkg, downstreamPkg⟩

theorem DiagonalTailSelectorPublicBudgetSource_real_seal_budget_nonescape
    [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name publicRow sealRead consumer hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorPublicBudgetSource r n mu k w d t s h c p name publicRow
        bundle pkg ->
      Cont t s sealRead ->
        Cont publicRow sealRead consumer ->
          PkgSig bundle sealRead pkg ->
            PkgSig bundle consumer pkg ->
              UnaryHistory s ∧ UnaryHistory publicRow ∧ UnaryHistory sealRead ∧
                UnaryHistory consumer ∧ Cont t s sealRead ∧
                  Cont publicRow sealRead consumer ∧ PkgSig bundle publicRow pkg ∧
                    PkgSig bundle sealRead pkg ∧ PkgSig bundle consumer pkg ∧
                      (Cont consumer (BHist.e0 hostTail) publicRow -> False) ∧
                        (Cont consumer (BHist.e1 hostTail) publicRow -> False) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro source sealRoute consumerRoute sealPkg consumerPkg
  obtain ⟨carrier, publicRoute, publicPkg⟩ := source
  obtain ⟨_rUnary, _nUnary, _muUnary, _kUnary, _wUnary, _dUnary, tUnary, sUnary,
    _hUnary, _cUnary, pUnary, nameUnary, _nMuK, _kWD, _pPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed pUnary nameUnary publicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnary sUnary sealRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed publicUnary sealUnary consumerRoute
  exact
    ⟨sUnary, publicUnary, sealUnary, consumerUnary, sealRoute, consumerRoute, publicPkg,
      sealPkg, consumerPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left consumerRoute hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right consumerRoute hostReturn)⟩

end BEDC.Derived.DiagonalTailSelectorUp
