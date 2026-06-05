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

theorem RefusalRegistry_nonescape [AskSetup] [PackageSetup]
    {B E G _C _S _V _T P N refused : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E →
      UnaryHistory G →
        Cont E G refused →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row refused ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row E ∨ hsame row G ∨ hsame row refused)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont E G refused ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory refused := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro entryUnary gateUnary refusalRoute provenancePkg namePkg
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed entryUnary gateUnary refusalRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro refused ⟨hsame_refl refused, refusedUnary⟩
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
        exact ⟨source.right, refusalRoute, provenancePkg, namePkg⟩
    }
  · exact refusedUnary

end BEDC.Derived.RefusalRegistryUp
