import BEDC.Derived.BishopCompletionModulusSelectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompletionModulusSelectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionModulusSelectionNameCertObligations [AskSetup] [PackageSetup]
    {M n k W D R E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    bishopCompletionModulusSelectionFields
        (BishopCompletionModulusSelectionUp.mk M n k W D R E H C P N) =
      [M, n, k, W, D, R, E, H, C, P, N] →
    UnaryHistory M →
    UnaryHistory n →
    UnaryHistory k →
    UnaryHistory W →
    UnaryHistory D →
    UnaryHistory R →
    UnaryHistory E →
    UnaryHistory H →
    UnaryHistory C →
    UnaryHistory P →
    UnaryHistory N →
    Cont M n k →
    Cont k W D →
    Cont W D R →
    Cont R E sealRead →
    PkgSig bundle P pkg →
    PkgSig bundle N pkg →
    SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row n ∨ hsame row k ∨ hsame row W ∨
            hsame row D ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M n k ∧ Cont k W D ∧ Cont W D R ∧
            Cont R E sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _fields mUnary nUnary _kUnary wUnary _dUnary rUnary eUnary _hUnary _cUnary
    _pUnary _nUnary thresholdRoute dyadicRoute handoffRoute sealRoute provenancePkg
    localNamePkg
  have kUnaryFromRoute : UnaryHistory k :=
    unary_cont_closed mUnary nUnary thresholdRoute
  have dUnaryFromRoute : UnaryHistory D :=
    unary_cont_closed kUnaryFromRoute wUnary dyadicRoute
  have rUnaryFromRoute : UnaryHistory R :=
    unary_cont_closed wUnary dUnaryFromRoute handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row n ∨ hsame row k ∨ hsame row W ∨
            hsame row D ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M n k ∧ Cont k W D ∧ Cont W D R ∧
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
                          (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, thresholdRoute, dyadicRoute, handoffRoute, sealRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.BishopCompletionModulusSelectionUp
