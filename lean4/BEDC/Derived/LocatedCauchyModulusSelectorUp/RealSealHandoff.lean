import BEDC.Derived.LocatedCauchyModulusSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.LocatedCauchyModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem LocatedCauchyModulusSelectorRealSealHandoff [AskSetup] [PackageSetup]
    {D W Q M L E H C P N windowRead locatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D W windowRead →
      Cont Q M locatedRead →
        Cont L E sealRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              locatedCauchyModulusSelectorFields
                    (LocatedCauchyModulusSelectorUp.mk D W Q M L E H C P N) =
                  [D, W, Q, M, L, E, H, C, P, N] ∧
                SemanticNameCert
                  (fun row : BHist => hsame row sealRead)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
                      hsame row L ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row sealRead)
                  (fun row : BHist =>
                    Cont D W windowRead ∧ Cont Q M locatedRead ∧
                      Cont L E sealRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg ∧ hsame row sealRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro windowRoute locatedRoute sealRoute provenancePkg localNamePkg
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead)
        (fun row : BHist =>
          hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
            hsame row L ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row sealRead)
        (fun row : BHist =>
          Cont D W windowRead ∧ Cont Q M locatedRead ∧ Cont L E sealRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row sealRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead (hsame_refl sealRead)
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
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨windowRoute, locatedRoute, sealRoute, provenancePkg, localNamePkg, source⟩
  }
  exact ⟨rfl, cert⟩

end BEDC.Derived.LocatedCauchyModulusSelectorUp
