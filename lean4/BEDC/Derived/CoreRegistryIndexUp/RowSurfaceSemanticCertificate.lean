import BEDC.Derived.CoreRegistryIndexUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CoreRegistryIndexUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CoreRegistryIndexCarrier_row_surface_semantic_certificate [AskSetup] [PackageSetup]
    {C T G D S F U O A H K P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle P pkg ->
      coreRegistryIndexFields (CoreRegistryIndexUp.mk C T G D S F U O A H K P N) =
          [C, T, G, D, S, F, U, O, A, H, K, P, N] ∧
        SemanticNameCert
          (fun row : BHist => hsame row P)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row G ∨ hsame row D ∨
              hsame row S ∨ hsame row F ∨ hsame row U ∨ hsame row O ∨
                hsame row A ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                  hsame row N)
          (fun row : BHist => hsame row P ∧ PkgSig bundle P pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro provenancePkg
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row P)
        (fun row : BHist =>
          hsame row C ∨ hsame row T ∨ hsame row G ∨ hsame row D ∨
            hsame row S ∨ hsame row F ∨ hsame row U ∨ hsame row O ∨
              hsame row A ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                hsame row N)
        (fun row : BHist => hsame row P ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro P (hsame_refl P)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inl source)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source, provenancePkg⟩
  }
  exact ⟨rfl, cert⟩

end BEDC.Derived.CoreRegistryIndexUp
