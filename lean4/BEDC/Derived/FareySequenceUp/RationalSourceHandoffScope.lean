import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRationalSourceHandoffScope [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N streamRead regularRead approximationRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont Q W streamRead ->
        Cont streamRead R regularRead ->
          Cont regularRead G approximationRead ->
            Cont approximationRead E realRead ->
              PkgSig bundle realRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨
                        hsame row E ∨ hsame row realRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
                    hsame ∧
                  UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory approximationRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier streamRoute regularRoute approximationRoute realRoute realPkg
  obtain ⟨_bUnary, _aUnary, _mUnary, _lUnary, _tUnary, _sUnary, _dUnary, qUnary,
    wUnary, rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty,
    _sEmpty, _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed qUnary wUnary streamRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary rUnary regularRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed regularUnary gUnary approximationRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed approximationUnary eUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨ hsame row E ∨
              hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, realPkg⟩
  }
  exact ⟨cert, streamUnary, regularUnary, approximationUnary, realUnary⟩

end BEDC.Derived.FareySequenceUp
