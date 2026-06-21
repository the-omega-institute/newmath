import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LpSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LpSpaceCarrier [AskSetup] [PackageSetup]
    (M R V N B I E H C Q A : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory V ∧ UnaryHistory N ∧
    UnaryHistory B ∧ UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory A ∧
        PkgSig bundle Q pkg ∧ PkgSig bundle A pkg

theorem LpSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M R V N B I E H C Q A read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LpSpaceCarrier M R V N B I E H C Q A bundle pkg →
      Cont I E read →
        PkgSig bundle read pkg →
          SemanticNameCert
              (fun row : BHist => hsame row read ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row V ∨ hsame row N ∨
                  hsame row B ∨ hsame row I ∨ hsame row E ∨ hsame row read)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont I E read ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle read pkg)
              hsame ∧
            UnaryHistory read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier readRoute readPkg
  obtain ⟨_mUnary, _rUnary, _vUnary, _nUnary, _bUnary, iUnary, eUnary, _hUnary,
    _cUnary, _qUnary, _aUnary, qPkg, _aPkg⟩ := carrier
  have readUnary : UnaryHistory read :=
    unary_cont_closed iUnary eUnary readRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row V ∨ hsame row N ∨
              hsame row B ∨ hsame row I ∨ hsame row E ∨ hsame row read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I E read ∧ PkgSig bundle Q pkg ∧
              PkgSig bundle read pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro read ⟨hsame_refl read, readUnary⟩
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
      exact ⟨source.right, readRoute, qPkg, readPkg⟩
  }
  exact ⟨cert, readUnary⟩

end BEDC.Derived.LpSpaceUp
