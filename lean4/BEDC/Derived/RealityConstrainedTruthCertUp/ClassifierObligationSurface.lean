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

theorem RealityConstrainedTruthCertClassifierObligationSurface [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N sourceSig classifierSig : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S Sigma sourceSig ->
      Cont sourceSig K classifierSig ->
        PkgSig bundle classifierSig pkg ->
          realityConstrainedTruthCertFields
              (RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
            [S, Sigma, K, T, U, D, I, L, F, N] ∧
            Cont S Sigma sourceSig ∧
              Cont sourceSig K classifierSig ∧
                PkgSig bundle classifierSig pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row classifierSig)
                    (fun row : BHist => hsame row sourceSig ∨ hsame row classifierSig)
                    (fun row : BHist => hsame row classifierSig ∧
                      PkgSig bundle classifierSig pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro sourceRoute classifierRoute classifierPkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierSig)
          (fun row : BHist => hsame row sourceSig ∨ hsame row classifierSig)
          (fun row : BHist =>
            hsame row classifierSig ∧ PkgSig bundle classifierSig pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro classifierSig (hsame_refl classifierSig)
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
      exact Or.inr source
    ledger_sound := by
      intro _row source
      exact ⟨source, classifierPkg⟩
  }
  exact ⟨rfl, sourceRoute, classifierRoute, classifierPkg, cert⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
