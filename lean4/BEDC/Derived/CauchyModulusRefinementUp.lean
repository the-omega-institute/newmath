import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# CauchyModulusRefinementUp finite carrier surface.
-/

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusRefinementCarrier [AskSetup] [PackageSetup]
    (m0 m1 u v t w q e h c p n : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
    UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
        Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧ Cont q e h ∧
          PkgSig bundle p pkg ∧ hsame h n

theorem CauchyModulusRefinementCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist => Cont q e h ∧ Cont h c row ∧ PkgSig bundle endpoint pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier hEndpoint endpointPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      _pUnary, _nUnary, m0m1u, uvt, twq, qeh, _pPkg, _hn⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary hEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, qeh, _pPkg, _hn⟩
          (hsame_refl endpoint))
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
      exact And.intro qeh (And.intro
        (cont_result_hsame_transport hEndpoint (hsame_symm source.right)) endpointPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport endpointUnary (hsame_symm source.right)) endpointPkg
  }

theorem CauchyModulusRefinement_source_meet_budget_chain [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
            hsame row w)
        (fun _row : BHist => Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
          PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro w (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl w))
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
      exact And.intro m0m1u (And.intro uvt (And.intro twq pPkg))
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport wUnary (hsame_symm source.right)) pPkg
  }

theorem CauchyModulusRefinement_window_readback_exhaustion [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
            hsame row q)
        (fun _row : BHist => Cont u v t ∧ Cont t w q ∧ PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro q (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl q))
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
      exact And.intro uvt (And.intro twq pPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport qUnary (hsame_symm source.right)) pPkg
  }

theorem CauchyModulusRefinement_root_readback_stability [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
            hsame row q)
        (fun _row : BHist => Cont t w q ∧ Cont q e h ∧ PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro q (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl q))
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
      exact And.intro twq (And.intro qeh pPkg)
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport qUnary (hsame_symm source.right)) pPkg
  }

theorem CauchyModulusRefinement_selector_budget_regseqrat_real_seal_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n w' q' e' h' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame w w' ->
        hsame e e' ->
          Cont t w' q' ->
            Cont q' e' h' ->
              hsame q q' ∧ hsame h h' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro carrier sameWindow sameSeal transportedWindow transportedSeal
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, carrierWindow,
      carrierSeal, _pPkg, _hn⟩
  have sameQ : hsame q q' :=
    cont_respects_hsame (hsame_refl t) sameWindow carrierWindow transportedWindow
  have sameH : hsame h h' :=
    cont_respects_hsame sameQ sameSeal carrierSeal transportedSeal
  exact ⟨sameQ, sameH⟩

theorem CauchyModulusRefinement_classifier_transport [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n m0' m1' u' v' t' w' q' e' h' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame m0 m0' ->
        hsame m1 m1' ->
          hsame v v' ->
            hsame w w' ->
              hsame e e' ->
                Cont m0' m1' u' ->
                  Cont u' v' t' ->
                    Cont t' w' q' ->
                      Cont q' e' h' ->
                        hsame u u' ∧ hsame t t' ∧ hsame q q' ∧ hsame h h' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro carrier sameM0 sameM1 sameV sameW sameE sourceRoute selectorRoute windowRoute sealRoute
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, carrierSource, carrierSelector,
      carrierWindow, carrierSeal, _pPkg, _hn⟩
  have sameU : hsame u u' :=
    cont_respects_hsame sameM0 sameM1 carrierSource sourceRoute
  have sameT : hsame t t' :=
    cont_respects_hsame sameU sameV carrierSelector selectorRoute
  have sameQ : hsame q q' :=
    cont_respects_hsame sameT sameW carrierWindow windowRoute
  have sameH : hsame h h' :=
    cont_respects_hsame sameQ sameE carrierSeal sealRoute
  exact ⟨sameU, sameT, sameQ, sameH⟩

theorem CauchyModulusRefinementCarrier_source_window_lock [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
          UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory selected ∧ Cont m0 m1 u ∧
            Cont u v t ∧ Cont t w selected ∧ PkgSig bundle p pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier selectedWindow
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, _qUnary, _eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedWindow
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, selectedUnary, m0m1u, uvt,
      selectedWindow, pPkg, hn⟩

theorem CauchyModulusRefinement_selector_stability_lock [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n v' t' q' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame v v' ->
        Cont u v' t' ->
          Cont t' w q' ->
            hsame t t' ∧ hsame q q' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro carrier sameSelector transportedSelector transportedWindow
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, carrierSelector,
      carrierWindow, _qeh, _pPkg, _hn⟩
  have sameT : hsame t t' :=
    cont_respects_hsame (hsame_refl u) sameSelector carrierSelector transportedSelector
  have sameQ : hsame q q' :=
    cont_respects_hsame sameT (hsame_refl w) carrierWindow transportedWindow
  exact ⟨sameT, sameQ⟩

theorem CauchyModulusRefinementCarrier_selector_seal_two_step_transport
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n vPrime tPrime qPrime ePrime hPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame v vPrime ->
        hsame e ePrime ->
          Cont u vPrime tPrime ->
            Cont tPrime w qPrime ->
              Cont qPrime ePrime hPrime ->
                hsame t tPrime ∧ hsame q qPrime ∧ hsame h hPrime := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro carrier sameSelector sameSeal transportedSelector transportedWindow transportedSeal
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, carrierSelector,
      carrierWindow, carrierSeal, _pPkg, _hn⟩
  have sameT : hsame t tPrime :=
    cont_respects_hsame (hsame_refl u) sameSelector carrierSelector transportedSelector
  have sameQ : hsame q qPrime :=
    cont_respects_hsame sameT (hsame_refl w) carrierWindow transportedWindow
  have sameH : hsame h hPrime :=
    cont_respects_hsame sameQ sameSeal carrierSeal transportedSeal
  exact ⟨sameT, sameQ, sameH⟩

theorem CauchyModulusRefinementCarrier_root_budget_stability [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
            hsame row t)
        (fun row : BHist =>
          Cont m0 m1 u ∧ Cont u v t ∧ hsame row t ∧ PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro t (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl t))
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
        intro row other sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨m0m1u, uvt, source.right, pPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport tUnary (hsame_symm source.right), pPkg⟩
  }

theorem CauchyModulusRefinementCarrier_root_threshold_public_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
                  UnaryHistory publicRead ∧ Cont m0 m1 u ∧ Cont u v t ∧
                    Cont t w selected ∧ Cont selected q readback ∧
                      Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                        PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧
                          hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic publicPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealHPublic
  exact
    ⟨selectedUnary, readbackUnary, sealReadUnary, publicReadUnary, m0m1u, uvt, tWSelected,
      selectedQReadback, readbackESeal, sealHPublic, pPkg, publicPkg, hn⟩

theorem CauchyModulusRefinementCarrier_root_source_binding [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont m0 u rootRead ->
        PkgSig bundle rootRead pkg ->
          UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory rootRead ∧
            Cont m0 m1 u ∧ Cont m0 u rootRead ∧ PkgSig bundle p pkg ∧
              PkgSig bundle rootRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier rootRoute rootPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed m0Unary uUnary rootRoute
  exact ⟨m0Unary, m1Unary, uUnary, rootUnary, m0m1u, rootRoute, pPkg, rootPkg, hn⟩

theorem CauchyModulusRefinementCarrier_root_selector_readback [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          PkgSig bundle readback pkg ->
            UnaryHistory selected /\ UnaryHistory readback /\ Cont m0 m1 u /\
              Cont u v t /\ Cont t w selected /\ Cont selected q readback /\
                PkgSig bundle p pkg /\ PkgSig bundle readback pkg /\ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier tWSelected selectedQReadback readbackPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  exact
    ⟨selectedUnary, readbackUnary, m0m1u, uvt, tWSelected, selectedQReadback, pPkg,
      readbackPkg, hn⟩

theorem CauchyModulusRefinementCarrier_root_classifier_transport_exactness [AskSetup]
    [PackageSetup]
    {m0 m1 u v t w q e h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory m0 /\ UnaryHistory m1 /\ UnaryHistory u /\ UnaryHistory v /\
            UnaryHistory t /\ UnaryHistory w /\ UnaryHistory q /\ UnaryHistory e /\
              UnaryHistory endpoint /\ Cont m0 m1 u /\ Cont u v t /\ Cont t w q /\
                Cont q e h /\ Cont h c endpoint /\ PkgSig bundle p pkg /\
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier endpointRoute endpointPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, qeh, pPkg, _hn⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary endpointRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, endpointUnary,
      m0m1u, uvt, twq, qeh, endpointRoute, pPkg, endpointPkg⟩

theorem CauchyModulusRefinementCarrier_bridged_route_surface [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont h c endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
              UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
                Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧ Cont q e h ∧
                  Cont h c endpoint ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle endpoint pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame ProbeBundle Pkg
  intro carrier endpointRoute endpointPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, endpointRoute, pPkg, endpointPkg,
      hn⟩

theorem CauchyModulusRefinementCarrier_root_window_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
                      hsame row publicRead)
                  (fun row : BHist =>
                    Cont m0 m1 u ∧ Cont u v t ∧ Cont t w selected ∧
                      Cont selected q readback ∧ Cont readback e sealRead ∧
                        Cont sealRead h row ∧ PkgSig bundle publicRead pkg)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic publicPkg
  rcases carrier with
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
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro
          ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
            cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
          (hsame_refl publicRead))
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
        ⟨m0m1u, uvt, tWSelected, selectedQReadback, readbackESeal,
          cont_result_hsame_transport sealHPublic (hsame_symm source.right), publicPkg⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport publicReadUnary (hsame_symm source.right), publicPkg⟩
  }

theorem CauchyModulusRefinementCarrier_shared_budget_pullback [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        Cont selected q readback →
          UnaryHistory selected ∧ UnaryHistory readback ∧ Cont m0 m1 u ∧ Cont u v t ∧
            Cont t w selected ∧ Cont selected q readback ∧ PkgSig bundle p pkg ∧
              hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier tWSelected selectedQReadback
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  exact
    ⟨selectedUnary, readbackUnary, m0m1u, uvt, tWSelected, selectedQReadback, pPkg,
      hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
