import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.DiscreteGronwallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem DiscreteGronwallNamecertObligations [AskSetup] [PackageSetup]
    {I U A B T Q R S H C _P _N step coeff majorant tail readback sealRow named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont I U step →
      Cont A B coeff →
        Cont step coeff majorant →
          Cont T Q tail →
            Cont tail R readback →
              Cont readback S sealRow →
                Cont H C named →
                  PkgSig bundle named pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row named ∧ PkgSig bundle named pkg)
                        (fun row : BHist =>
                          hsame row I ∨ hsame row U ∨ hsame row A ∨ hsame row B ∨
                            hsame row T ∨ hsame row Q ∨ hsame row R ∨ hsame row S ∨
                              hsame row named)
                        (fun row : BHist =>
                          PkgSig bundle named pkg ∧ hsame row named ∧
                            Cont readback S sealRow)
                        hsame ∧
                      Cont I U step ∧ Cont A B coeff ∧ Cont step coeff majorant ∧
                        Cont readback S sealRow := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro stepRoute coeffRoute majorantRoute _tailRoute _readbackRoute sealRoute _namedRoute
    pkgNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ PkgSig bundle named pkg)
          (fun row : BHist =>
            hsame row I ∨ hsame row U ∨ hsame row A ∨ hsame row B ∨ hsame row T ∨
              hsame row Q ∨ hsame row R ∨ hsame row S ∨ hsame row named)
          (fun row : BHist =>
            PkgSig bundle named pkg ∧ hsame row named ∧ Cont readback S sealRow)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro named ⟨hsame_refl named, pkgNamed⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨pkgNamed, sourceRow.left, sealRoute⟩
    }
  exact ⟨cert, stepRoute, coeffRoute, majorantRoute, sealRoute⟩

end BEDC.Derived.DiscreteGronwallUp
