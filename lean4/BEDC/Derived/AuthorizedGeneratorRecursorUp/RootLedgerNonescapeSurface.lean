import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootLedgerNonescapeSurface
    [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap
      name ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont gap name ledgerRead →
      UnaryHistory gap →
        UnaryHistory name →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row gap ∨ hsame row name ∨ hsame row ledgerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont gap name ledgerRead ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              authorizedGeneratorRecursorFromEventFlow
                  (authorizedGeneratorRecursorToEventFlow
                    (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                      descent output audit transport routes provenance gap name)) =
                some
                  (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                    descent output audit transport routes provenance gap name) ∧
                UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledgerRoute gapUnary nameUnary provenancePkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed gapUnary nameUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row gap ∨ hsame row name ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont gap name ledgerRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerRoute, provenancePkg⟩
  }
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
            audit transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  exact ⟨cert, roundTrip, ledgerUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
