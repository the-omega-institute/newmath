import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealModulusFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealModulusFusionCarrier [AskSetup] [PackageSetup]
    (X M T W R S E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
  Prop :=
  UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
    UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory N ∧ Cont X M T ∧ Cont T W R ∧ Cont R S E ∧
        Cont H C N ∧ PkgSig bundle P pkg

theorem RealModulusFusionNamecertObligations [AskSetup] [PackageSetup]
    {X M T W R S E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealModulusFusionCarrier X M T W R S E H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row M ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
              hsame row S ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame ∧
        UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory W ∧
          UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory E := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier
  obtain ⟨xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary, _hUnary, _cUnary,
    nUnary, _sourceModulus, _tailWindow, _handoffSeal, _hContCName, pkgRow⟩ := carrier
  have sourceName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row M ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
              hsame row S ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        cases same
        exact source
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
                        (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgRow⟩
  }
  exact ⟨cert, xUnary, mUnary, tUnary, wUnary, rUnary, sUnary, eUnary⟩

end BEDC.Derived.RealModulusFusionUp
