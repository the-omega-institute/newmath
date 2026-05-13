import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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

end BEDC.Derived.DiagonalTailSelectorUp
