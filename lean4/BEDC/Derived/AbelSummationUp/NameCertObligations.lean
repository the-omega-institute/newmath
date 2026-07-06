import BEDC.Derived.AbelSummationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AbelSummationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

def AbelSummationCarrier [AskSetup] [PackageSetup]
    (S A D B T R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: AbelSummationUp BHist ProbeBundle Pkg UnaryHistory PkgSig
  FieldFaithful.fields (AbelSummationUp.mk S A D B T R E H C P N) =
    [S, A, D, B, T, R, E, H, C, P, N] ∧
    UnaryHistory S ∧ UnaryHistory A ∧ UnaryHistory D ∧ UnaryHistory B ∧
      UnaryHistory T ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem AbelSummationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S A D B T R E H C P N nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AbelSummationCarrier S A D B T R E H C P N bundle pkg ->
      PkgSig bundle N pkg ->
        Cont C N nameRead ->
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row A ∨ hsame row D ∨ hsame row B ∨
                  hsame row T ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C N nameRead ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: AbelSummationCarrier BHist ProbeBundle Pkg Cont SemanticNameCert
  intro carrier namePkg nameRoute
  obtain ⟨fieldRows, _sUnary, _aUnary, _dUnary, _bUnary, _tUnary, _rUnary,
    _eUnary, _hUnary, cUnary, _pUnary, nUnary, _pPkg, _storedNamePkg⟩ := carrier
  cases fieldRows
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed cUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row D ∨ hsame row B ∨
              hsame row T ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N nameRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nameRoute, namePkg⟩
  }
  exact ⟨cert, nameReadUnary⟩

end BEDC.Derived.AbelSummationUp
