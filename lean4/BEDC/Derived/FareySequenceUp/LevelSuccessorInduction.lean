import BEDC.Derived.FareySequenceUp.NameCertObligations

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceLevelSuccessorInduction [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N levelRead successorRead densityRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont B A levelRead →
        Cont levelRead M successorRead →
          Cont successorRead L densityRead →
            Cont densityRead N namedRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                          hsame row levelRead ∨ hsame row successorRead ∨
                            hsame row densityRead ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont B A levelRead ∧
                          Cont levelRead M successorRead ∧
                            Cont successorRead L densityRead ∧
                              Cont densityRead N namedRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory levelRead ∧ UnaryHistory successorRead ∧
                      UnaryHistory densityRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier levelRoute successorRoute densityRoute namedRoute provenancePkg namePkg
  obtain ⟨bUnary, aUnary, mUnary, lUnary, _tUnary, _sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed bUnary aUnary levelRoute
  have successorUnary : UnaryHistory successorRead :=
    unary_cont_closed levelUnary mUnary successorRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed successorUnary lUnary densityRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed densityUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
              hsame row levelRead ∨ hsame row successorRead ∨
                hsame row densityRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A levelRead ∧ Cont levelRead M successorRead ∧
              Cont successorRead L densityRead ∧ Cont densityRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, levelRoute, successorRoute, densityRoute, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, levelUnary, successorUnary, densityUnary, namedUnary⟩

end BEDC.Derived.FareySequenceUp
