import BEDC.Derived.BrouwerBarInductionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BrouwerBarInductionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BrouwerBarInductionPrefixStability [AskSetup] [PackageSetup]
    {t b m i w r e h c p n prefixTree restrictedBar restrictedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame t prefixTree →
      hsame b restrictedBar →
        hsame i restrictedReplay →
          PkgSig bundle p pkg →
            SemanticNameCert
                (fun row : BHist => hsame row prefixTree ∧ PkgSig bundle p pkg)
                (fun row : BHist =>
                  hsame row prefixTree ∨ hsame row restrictedBar ∨
                    hsame row restrictedReplay)
                (fun row : BHist => hsame row prefixTree ∧ PkgSig bundle p pkg)
                hsame ∧
              brouwerBarInductionFromEventFlow
                  (brouwerBarInductionToEventFlow
                    (BrouwerBarInductionUp.mk prefixTree restrictedBar m restrictedReplay w r e h
                      c p n)) =
                some
                  (BrouwerBarInductionUp.mk prefixTree restrictedBar m restrictedReplay w r e h
                    c p n) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro _treeSame _barSame _replaySame provenancePkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row prefixTree ∧ PkgSig bundle p pkg)
          (fun row : BHist =>
            hsame row prefixTree ∨ hsame row restrictedBar ∨ hsame row restrictedReplay)
          (fun row : BHist => hsame row prefixTree ∧ PkgSig bundle p pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro prefixTree ⟨hsame_refl prefixTree, provenancePkg⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inl source.left
      ledger_sound := by
        intro _row source
        exact source
    }
  have roundTrip :
      brouwerBarInductionFromEventFlow
          (brouwerBarInductionToEventFlow
            (BrouwerBarInductionUp.mk prefixTree restrictedBar m restrictedReplay w r e h c p n)) =
        some
          (BrouwerBarInductionUp.mk prefixTree restrictedBar m restrictedReplay w r e h c p n) :=
    BrouwerBarInductionTasteGate_single_carrier_alignment.right.left
      (BrouwerBarInductionUp.mk prefixTree restrictedBar m restrictedReplay w r e h c p n)
  exact ⟨cert, roundTrip⟩

end BEDC.Derived.BrouwerBarInductionUp
