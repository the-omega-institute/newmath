import BEDC.Derived.BishopCompletionModulusUp.TasteGate

namespace BEDC.Derived.BishopCompletionModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionModulusCarrier_obligation_package [AskSetup] [PackageSetup]
    {M S n k W D R E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionModulusCarrier M S n k W D R E H C P N bundle pkg →
    Cont R E sealRead →
    SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row S ∨ hsame row n ∨ hsame row k ∨
            hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M n k ∧ Cont S k W ∧ Cont W D R ∧
            Cont R E sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame ∧
      UnaryHistory sealRead ∧ Cont M n k ∧ Cont S k W ∧ Cont W D R ∧
        Cont R E sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sealRoute
  obtain ⟨_mUnary, _sUnary, _nUnary, _kUnary, _wUnary, _dUnary, rUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _localNameUnary, modulusRoute, windowRoute,
      handoffRoute, _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row S ∨ hsame row n ∨ hsame row k ∨
            hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M n k ∧ Cont S k W ∧ Cont W D R ∧
            Cont R E sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, windowRoute, handoffRoute, sealRoute,
          provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, sealUnary, modulusRoute, windowRoute, handoffRoute, sealRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.BishopCompletionModulusUp
