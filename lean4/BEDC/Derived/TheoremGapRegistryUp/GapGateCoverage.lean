import BEDC.Derived.TheoremGapRegistryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TheoremGapRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheoremGapRegistry_gap_gate_coverage [AskSetup] [PackageSetup]
    {G C F A P N covered : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G →
      UnaryHistory C →
        Cont G C covered →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row covered ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row G ∨ hsame row C ∨ hsame row F ∨ hsame row covered)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont G C covered ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory covered := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro gapUnary coverageUnary coverageRoute provenancePkg namePkg
  have coveredUnary : UnaryHistory covered :=
    unary_cont_closed gapUnary coverageUnary coverageRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro covered ⟨hsame_refl covered, coveredUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, coverageRoute, provenancePkg, namePkg⟩
    }
  · exact coveredUnary

end BEDC.Derived.TheoremGapRegistryUp
