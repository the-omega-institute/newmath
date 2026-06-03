import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FractionalPartUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FractionalPartCarrier [AskSetup] [PackageSetup]
    (R I F B D S G H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory R ∧ UnaryHistory I ∧ UnaryHistory F ∧ UnaryHistory B ∧ UnaryHistory D ∧
    UnaryHistory S ∧ UnaryHistory G ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont R I F ∧ Cont B D S ∧ Cont S G F ∧ Cont H C P ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem FractionalPartCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {R I F B D S G H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FractionalPartCarrier R I F B D S G H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FractionalPartCarrier R I F B D S G H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          FractionalPartCarrier R I F B D S G H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          FractionalPartCarrier R I F B D S G H C P N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrier, hsame_refl N⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem FractionalPartCarrier_real_int_handoff [AskSetup] [PackageSetup]
    {R I F B D S G H C P N residualWindow decimalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FractionalPartCarrier R I F B D S G H C P N bundle pkg →
      Cont F S residualWindow →
        Cont residualWindow G decimalRead →
          PkgSig bundle decimalRead pkg →
            UnaryHistory R ∧ UnaryHistory I ∧ UnaryHistory F ∧ UnaryHistory B ∧
              UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory G ∧
                UnaryHistory residualWindow ∧ UnaryHistory decimalRead ∧ Cont R I F ∧
                  Cont B D S ∧ Cont S G F ∧ Cont F S residualWindow ∧
                    Cont residualWindow G decimalRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle decimalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier residualWindowRoute decimalReadRoute decimalReadPkg
  obtain ⟨rUnary, iUnary, fUnary, bUnary, dUnary, sUnary, gUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, realIntResidual, bracketToleranceStream, streamRegularResidual,
    _nameRoute, provenancePkg, _localNamePkg⟩ := carrier
  have residualWindowUnary : UnaryHistory residualWindow :=
    unary_cont_closed fUnary sUnary residualWindowRoute
  have decimalReadUnary : UnaryHistory decimalRead :=
    unary_cont_closed residualWindowUnary gUnary decimalReadRoute
  exact
    ⟨rUnary, iUnary, fUnary, bUnary, dUnary, sUnary, gUnary, residualWindowUnary,
      decimalReadUnary, realIntResidual, bracketToleranceStream, streamRegularResidual,
      residualWindowRoute, decimalReadRoute, provenancePkg, decimalReadPkg⟩

end BEDC.Derived.FractionalPartUp
