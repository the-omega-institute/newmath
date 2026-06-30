import BEDC.Derived.ClosedConsistencyAssemblyUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ClosedConsistencyAssemblyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ClosedConsistencyAssemblySiblingRouting
    {x : ClosedConsistencyAssemblyUp} {siblingRead routeRead : BHist} :
    siblingRead ∈ closedConsistencyAssemblyFields x →
      UnaryHistory siblingRead →
        Cont siblingRead siblingRead routeRead →
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                row ∈ closedConsistencyAssemblyFields x ∨ hsame row routeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont siblingRead siblingRead routeRead)
              hsame ∧
            UnaryHistory routeRead ∧ Cont siblingRead siblingRead routeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro siblingMember siblingUnary siblingRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed siblingUnary siblingUnary siblingRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist => row ∈ closedConsistencyAssemblyFields x ∨ hsame row routeRead)
          (fun row : BHist => UnaryHistory row ∧ Cont siblingRead siblingRead routeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, siblingRoute⟩
  }
  exact ⟨cert, routeUnary, siblingRoute⟩

end BEDC.Derived.ClosedConsistencyAssemblyUp
