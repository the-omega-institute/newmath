import BEDC.Derived.TypeLikeUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TypeLikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem TypeLikeNameCert_obligations [AskSetup] [PackageSetup]
    {B F Q E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B F (append B F) →
      Cont F Q (append F Q) →
        Cont Q E (append Q E) →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row N)
                (fun row : BHist =>
                  hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
                (fun row : BHist => hsame row N ∧ PkgSig bundle N pkg)
                hsame ∧
              Cont H C (append H C) ∧
                Cont C P (append C P) ∧ Cont P N (append P N) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame NameCert
  intro _baseFiberRoute _fiberClassifierRoute _classifierExactnessRoute namePkg
  have source : (fun row : BHist => hsame row N) N := by
    exact hsame_refl N
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N)
          (fun row : BHist =>
            hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row N ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N source
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
        intro _row _other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro _row rowSource
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rowSource))))))
    ledger_sound := by
      intro _row rowSource
      exact ⟨rowSource, namePkg⟩
  }
  exact ⟨cert, rfl, rfl, rfl⟩

end BEDC.Derived.TypeLikeUp
