import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetCarrier_deleted_gap_ledger_exhaustion [AskSetup] [PackageSetup]
    {T G I D R E gapRead deletedRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont G I gapRead ->
      Cont gapRead D deletedRead ->
        Cont deletedRead R regularRead ->
          PkgSig bundle E pkg ->
            UnaryHistory G ->
              UnaryHistory I ->
                UnaryHistory D ->
                  UnaryHistory R ->
                    SemanticNameCert
                        (fun row : BHist => hsame row deletedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row G ∨ hsame row I ∨ hsame row gapRead ∨ hsame row D ∨
                            hsame row deletedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle E pkg ∧
                            Cont gapRead D deletedRead)
                        hsame ∧
                      UnaryHistory gapRead ∧ UnaryHistory deletedRead ∧
                        UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro gapRoute deletedRoute regularRoute packageE gapUnary intervalUnary deletedUnary
    regularUnary
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed gapUnary intervalUnary gapRoute
  have deletedReadUnary : UnaryHistory deletedRead :=
    unary_cont_closed gapReadUnary deletedUnary deletedRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed deletedReadUnary regularUnary regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row deletedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row I ∨ hsame row gapRead ∨ hsame row D ∨
              hsame row deletedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle E pkg ∧ Cont gapRead D deletedRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro deletedRead ⟨hsame_refl deletedRead, deletedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, packageE, deletedRoute⟩
  }
  exact ⟨cert, gapReadUnary, deletedReadUnary, regularReadUnary⟩

end BEDC.Derived.CantorSetUp
