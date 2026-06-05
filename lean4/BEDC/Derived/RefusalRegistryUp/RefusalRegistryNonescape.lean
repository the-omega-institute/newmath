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

theorem RefusalRegistry_public_export_surface [AskSetup] [PackageSetup]
    {B E G C S V T P N refused exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory E →
        UnaryHistory G →
          UnaryHistory C →
            Cont B E refused →
              Cont E G refused →
                Cont refused C exported →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row refused ∨ hsame row exported) ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row B ∨ hsame row E ∨ hsame row G ∨ hsame row C ∨
                              hsame row S ∨ hsame row V ∨ hsame row T ∨ hsame row P ∨
                                hsame row N ∨ hsame row refused ∨ hsame row exported)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont B E refused ∧ Cont E G refused ∧
                              Cont refused C exported ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory exported := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro baseUnary entryUnary gateUnary claimUnary baseEntryRoute entryGateRoute exportRoute
    provenancePkg namePkg
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed baseUnary entryUnary baseEntryRoute
  have refusedUnaryFromGate : UnaryHistory refused :=
    unary_cont_closed entryUnary gateUnary entryGateRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed refusedUnary claimUnary exportRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro refused ⟨Or.inl (hsame_refl refused), refusedUnaryFromGate⟩
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
            | inl sameRefused =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameRefused)
            | inr sameExported =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameExported)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
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
            exact sameExported
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, baseEntryRoute, entryGateRoute, exportRoute, provenancePkg,
            namePkg⟩
    }
  · exact exportedUnary

end BEDC.Derived.RefusalRegistryUp
