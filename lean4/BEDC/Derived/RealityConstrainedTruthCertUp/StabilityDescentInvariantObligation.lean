import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate

theorem RealityConstrainedTruthCertStabilityDescentInvariantObligation
    [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N towerStable descentRead invariantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T U towerStable ->
      Cont towerStable D descentRead ->
        Cont descentRead I invariantRead ->
          PkgSig bundle invariantRead pkg ->
            realityConstrainedTruthCertFields
                (RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
                [S, Sigma, K, T, U, D, I, L, F, N] ∧
              SemanticNameCert
                  (fun row : BHist => hsame row invariantRead)
                  (fun row : BHist =>
                    hsame row towerStable ∨ hsame row descentRead ∨
                      hsame row invariantRead)
                  (fun row : BHist =>
                    hsame row invariantRead ∧ PkgSig bundle invariantRead pkg)
                  hsame ∧
                Cont T U towerStable ∧
                  Cont towerStable D descentRead ∧
                    Cont descentRead I invariantRead ∧
                      PkgSig bundle invariantRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro towerRoute descentRoute invariantRoute invariantPkg
  have sourceInvariant :
      (fun row : BHist => hsame row invariantRead) invariantRead := by
    exact hsame_refl invariantRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row invariantRead)
        (fun row : BHist =>
          hsame row towerStable ∨ hsame row descentRead ∨ hsame row invariantRead)
        (fun row : BHist =>
          hsame row invariantRead ∧ PkgSig bundle invariantRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro invariantRead sourceInvariant
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source)
    ledger_sound := by
      intro _row source
      exact ⟨source, invariantPkg⟩
  }
  exact ⟨rfl, cert, towerRoute, descentRoute, invariantRoute, invariantPkg⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
