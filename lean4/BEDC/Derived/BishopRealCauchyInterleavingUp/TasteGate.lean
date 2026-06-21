import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealCauchyInterleavingCarrier [AskSetup] [PackageSetup]
    (S0 S1 W0 W1 D0 D1 J R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory S0 ∧ UnaryHistory S1 ∧ UnaryHistory W0 ∧ UnaryHistory W1 ∧
    UnaryHistory D0 ∧ UnaryHistory D1 ∧ UnaryHistory J ∧ UnaryHistory R ∧
      UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BishopRealCauchyInterleavingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S0 S1 W0 W1 D0 D1 J R E H C P N read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealCauchyInterleavingCarrier S0 S1 W0 W1 D0 D1 J R E H C P N bundle pkg →
      Cont J R read →
        PkgSig bundle read pkg →
          SemanticNameCert
              (fun row : BHist => hsame row read ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S0 ∨ hsame row S1 ∨ hsame row W0 ∨ hsame row W1 ∨
                  hsame row D0 ∨ hsame row D1 ∨ hsame row J ∨ hsame row R ∨
                    hsame row E ∨ hsame row read)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont J R read ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle read pkg)
              hsame ∧
            UnaryHistory read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier readRoute readPkg
  obtain ⟨_s0Unary, _s1Unary, _w0Unary, _w1Unary, _d0Unary, _d1Unary, jUnary, rUnary,
    _eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _pPkg, nPkg⟩ := carrier
  have readUnary : UnaryHistory read :=
    unary_cont_closed jUnary rUnary readRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S0 ∨ hsame row S1 ∨ hsame row W0 ∨ hsame row W1 ∨
              hsame row D0 ∨ hsame row D1 ∨ hsame row J ∨ hsame row R ∨
                hsame row E ∨ hsame row read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J R read ∧ PkgSig bundle N pkg ∧
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, readRoute, nPkg, readPkg⟩
  }
  exact ⟨cert, readUnary⟩

end BEDC.Derived.BishopRealCauchyInterleavingUp
