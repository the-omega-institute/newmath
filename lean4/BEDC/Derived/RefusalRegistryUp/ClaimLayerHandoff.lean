import BEDC.Derived.RefusalRegistryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RefusalRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RefusalRegistry_claim_layer_handoff [AskSetup] [PackageSetup]
    {B E G C S V T P N handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory E →
        Cont B E handoff →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row E ∨ hsame row C ∨ hsame row handoff)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B E handoff ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory handoff := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro blockedUnary refusalUnary handoffRoute provenancePkg namePkg
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed blockedUnary refusalUnary handoffRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro handoff ⟨hsame_refl handoff, handoffUnary⟩
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
        exact ⟨source.right, handoffRoute, provenancePkg, namePkg⟩
    }
  · exact handoffUnary

end BEDC.Derived.RefusalRegistryUp
