import BEDC.Derived.CandidateEvidenceSNRouteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CandidateEvidenceSNRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CandidateEvidenceSNRoute_no_infinite_boundary [AskSetup] [PackageSetup]
    {E K M A I H C P N noInfiniteRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (Cont E I noInfiniteRead ∨ Cont K I noInfiniteRead ∨
        Cont M I noInfiniteRead ∨ Cont A I noInfiniteRead) →
      PkgSig bundle P pkg →
        PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row noInfiniteRead ∧
                  (Cont E I noInfiniteRead ∨ Cont K I noInfiniteRead ∨
                    Cont M I noInfiniteRead ∨ Cont A I noInfiniteRead))
              (fun row : BHist =>
                hsame row E ∨ hsame row K ∨ hsame row M ∨ hsame row A ∨
                  hsame row I ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row noInfiniteRead)
              (fun row : BHist =>
                hsame row noInfiniteRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro route provenancePkg namePkg
  exact {
    core := {
      carrier_inhabited := Exists.intro noInfiniteRead ⟨hsame_refl noInfiniteRead, route⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
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
                      (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }

end BEDC.Derived.CandidateEvidenceSNRouteUp
