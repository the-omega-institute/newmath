import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealInverseUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealInverseCarrier [AskSetup] [PackageSetup]
    (x a p w r s h c l n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory x ∧ UnaryHistory a ∧ UnaryHistory p ∧ UnaryHistory w ∧ UnaryHistory r ∧
    UnaryHistory s ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory l ∧ UnaryHistory n ∧
      Cont a w r ∧ Cont p r s ∧ Cont c l n ∧ PkgSig bundle l pkg ∧ PkgSig bundle n pkg

theorem RealInverseNameCertObligations [AskSetup] [PackageSetup]
    {x a p w r s h c l n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealInverseCarrier x a p w r s h c l n bundle pkg →
      SemanticNameCert
        (fun row : BHist => RealInverseCarrier x a p w r s h c l n bundle pkg ∧ hsame row n)
        (fun row : BHist => RealInverseCarrier x a p w r s h c l n bundle pkg ∧ hsame row n)
        (fun row : BHist => RealInverseCarrier x a p w r s h c l n bundle pkg ∧ hsame row n)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro n ⟨carrier, hsame_refl n⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.RealInverseUp
