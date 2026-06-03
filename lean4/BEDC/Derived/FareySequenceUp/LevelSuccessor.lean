import BEDC.Derived.FareySequenceUp.NameCertObligations

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceLevelSuccessor [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N levelRead successorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont L T levelRead →
        Cont levelRead M successorRead →
          PkgSig bundle successorRead pkg →
            UnaryHistory levelRead ∧ UnaryHistory successorRead ∧
              SemanticNameCert
                (fun row : BHist => hsame row successorRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                    hsame row T ∨ hsame row successorRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle successorRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier levelRoute successorRoute successorPkg
  obtain ⟨_bUnary, _aUnary, mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed lUnary tUnary levelRoute
  have successorUnary : UnaryHistory successorRead :=
    unary_cont_closed levelUnary mUnary successorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row successorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
              hsame row T ∨ hsame row successorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle successorRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro successorRead ⟨hsame_refl successorRead, successorUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, successorPkg⟩
  }
  exact ⟨levelUnary, successorUnary, cert⟩

end BEDC.Derived.FareySequenceUp
