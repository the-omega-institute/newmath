import BEDC.Derived.CevaUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CevaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CevaCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T S L X H C P N sideRead concurrenceRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory S →
        UnaryHistory L →
          UnaryHistory X →
            Cont T S sideRead →
              Cont L X concurrenceRead →
                Cont sideRead concurrenceRead named →
                  PkgSig bundle P pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row named ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row T ∨ hsame row S ∨ hsame row L ∨ hsame row X ∨
                            hsame row sideRead ∨ hsame row concurrenceRead ∨
                              hsame row named)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont T S sideRead ∧
                            Cont L X concurrenceRead ∧ Cont sideRead concurrenceRead named ∧
                              PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory sideRead ∧ UnaryHistory concurrenceRead ∧
                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro tUnary sUnary lUnary xUnary sideRoute concurrenceRoute namedRoute packageRead
  have sideUnary : UnaryHistory sideRead :=
    unary_cont_closed tUnary sUnary sideRoute
  have concurrenceUnary : UnaryHistory concurrenceRead :=
    unary_cont_closed lUnary xUnary concurrenceRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sideUnary concurrenceUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row L ∨ hsame row X ∨
              hsame row sideRead ∨ hsame row concurrenceRead ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T S sideRead ∧ Cont L X concurrenceRead ∧
              Cont sideRead concurrenceRead named ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sideRoute, concurrenceRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, sideUnary, concurrenceUnary, namedUnary⟩

end BEDC.Derived.CevaUp
