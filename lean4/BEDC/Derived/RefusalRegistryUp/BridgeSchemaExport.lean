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

theorem RefusalRegistry_bridge_schema_export [AskSetup] [PackageSetup]
    {B E G C S V T P N refused exported handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory E →
        UnaryHistory G →
          UnaryHistory C →
            Cont B E handoff →
              Cont E G refused →
                Cont refused C exported →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row handoff ∨ hsame row refused ∨
                              hsame row exported) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row B ∨ hsame row E ∨ hsame row G ∨ hsame row C ∨
                              hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row P ∨
                                hsame row N ∨ hsame row handoff ∨ hsame row refused ∨
                                  hsame row exported)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont B E handoff ∧ Cont E G refused ∧
                              Cont refused C exported ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory exported := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro baseUnary entryUnary gateUnary cannotUnary handoffRoute refusalRoute exportRoute
    provenancePkg namePkg
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed baseUnary entryUnary handoffRoute
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed entryUnary gateUnary refusalRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed refusedUnary cannotUnary exportRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro exported ⟨Or.inr (Or.inr (hsame_refl exported)), exportedUnary⟩
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
          constructor
          · cases source.left with
            | inl sameHandoff =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameHandoff)
            | inr rest =>
                cases rest with
                | inl sameRefused =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRefused))
                | inr sameExported =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameExported))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameHandoff =>
            right
            right
            right
            right
            right
            right
            right
            right
            right
            left
            exact sameHandoff
        | inr rest =>
            cases rest with
            | inl sameRefused =>
                right
                right
                right
                right
                right
                right
                right
                right
                right
                right
                left
                exact sameRefused
            | inr sameExported =>
                right
                right
                right
                right
                right
                right
                right
                right
                right
                right
                right
                exact sameExported
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, handoffRoute, refusalRoute, exportRoute, provenancePkg,
            namePkg⟩
    }
  · exact exportedUnary

end BEDC.Derived.RefusalRegistryUp
