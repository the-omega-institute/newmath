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

end BEDC.Derived.CauchyModulusRefinementUp
