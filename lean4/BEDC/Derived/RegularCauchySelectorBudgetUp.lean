import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RegularCauchySelectorBudgetUp finite tail-precision surface and carrier.
-/

namespace BEDC.Derived.RegularCauchySelectorBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySelectorBudgetTailPrecisionSource [AskSetup] [PackageSetup]
    (mu w s r d e h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory mu ∧ UnaryHistory w ∧ UnaryHistory s ∧ UnaryHistory r ∧
    UnaryHistory d ∧ UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory n ∧ Cont d mu w ∧ Cont w s r ∧
        Cont r e c ∧ PkgSig bundle p pkg

theorem RegularCauchySelectorBudgetCarrier_tail_precision_exactness [AskSetup]
    [PackageSetup]
    {mu w s r d e h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySelectorBudgetTailPrecisionSource mu w s r d e h c p n bundle pkg ->
      Cont h c endpoint ->
        UnaryHistory endpoint ∧ Cont d mu w ∧ Cont w s r ∧ Cont r e c ∧
          Cont h c endpoint ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro source endpointRoute
  obtain ⟨_muUnary, _wUnary, _sUnary, _rUnary, _dUnary, _eUnary, hUnary, cUnary,
    _pUnary, _nUnary, precisionWindow, windowStream, regseqSeal, pkgSig⟩ := source
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary endpointRoute
  exact ⟨endpointUnary, precisionWindow, windowStream, regseqSeal, endpointRoute, pkgSig⟩

def RegularCauchySelectorBudgetCarrier [AskSetup] [PackageSetup]
    (mu w s r e h c p name : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory mu ∧ UnaryHistory w ∧ UnaryHistory s ∧ UnaryHistory r ∧
    UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧
      UnaryHistory name ∧ Cont mu w s ∧ PkgSig bundle p pkg

theorem RegularCauchySelectorBudgetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {mu w s r e h c p name consumer : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySelectorBudgetCarrier mu w s r e h c p name bundle pkg ->
      Cont s r e ->
        Cont e h consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory mu ∧ UnaryHistory w ∧ UnaryHistory s ∧ UnaryHistory r ∧
              UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧
                UnaryHistory name ∧ UnaryHistory consumer ∧ Cont mu w s ∧ Cont s r e ∧
                  Cont e h consumer ∧ PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row p ∧ UnaryHistory row)
                      (fun row : BHist => hsame row p)
                      (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier streamWitness sealConsumer consumerPkg
  obtain ⟨muUnary, wUnary, sUnary, rUnary, eUnary, hUnary, cUnary, pUnary, nameUnary,
    modulusWindow, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed eUnary hUnary sealConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro p ⟨hsame_refl p, pUnary⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨muUnary, wUnary, sUnary, rUnary, eUnary, hUnary, cUnary, pUnary, nameUnary,
      consumerUnary, modulusWindow, streamWitness, sealConsumer, provenancePkg, consumerPkg, cert⟩

theorem RegularCauchySelectorBudgetCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {mu w s r e h c p name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySelectorBudgetCarrier mu w s r e h c p name bundle pkg ->
      Cont w s r ->
        Cont r e consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory w ∧ UnaryHistory s ∧ UnaryHistory r ∧ UnaryHistory e ∧
              UnaryHistory consumer ∧ Cont mu w s ∧ Cont w s r ∧
                Cont r e consumer ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowStream streamConsumer consumerPkg
  obtain ⟨_muUnary, wUnary, sUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nameUnary, modulusWindow, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed rUnary eUnary streamConsumer
  exact
    ⟨wUnary, sUnary, rUnary, eUnary, consumerUnary, modulusWindow, windowStream,
      streamConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.RegularCauchySelectorBudgetUp
