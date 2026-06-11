import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionAdjunctionTriangleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionAdjunctionTriangleCarrier [AskSetup] [PackageSetup]
    (F A U I R W D E H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory F ∧ UnaryHistory A ∧ UnaryHistory U ∧ UnaryHistory I ∧
    UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyCompletionAdjunctionTriangleNamecertObligations [AskSetup]
    [PackageSetup] {F A U I R W D E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionAdjunctionTriangleCarrier F A U I R W D E H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            CauchyCompletionAdjunctionTriangleCarrier F A U I R W D E H C P N
              bundle pkg ∧ hsame row N)
          (fun row : BHist =>
            CauchyCompletionAdjunctionTriangleCarrier F A U I R W D E H C P N
              bundle pkg ∧ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame UnaryHistory SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_fUnary, _aUnary, _uUnary, _iUnary, _rUnary, _wUnary, _dUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, nUnary, _pkgP, pkgN⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrierWitness, hsame_refl N⟩
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
      exact ⟨unary_transport nUnary (hsame_symm source.right), pkgN⟩
  }

end BEDC.Derived.CauchyCompletionAdjunctionTriangleUp
