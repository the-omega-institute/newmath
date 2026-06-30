import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FanCompactUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def FanCompactCarrier (B L T W R I H C P N : BHist) : Prop :=
  UnaryHistory B ∧ UnaryHistory L ∧ UnaryHistory T ∧ UnaryHistory W ∧
    UnaryHistory R ∧ UnaryHistory I ∧ UnaryHistory H ∧ UnaryHistory C ∧ Cont B L T ∧
      Cont T W R ∧ Cont C P N

theorem FanCompactCarrier_finite_bar_induction
    {B L T W R I H C P N barRead rootRead : BHist} :
    FanCompactCarrier B L T W R I H C P N ->
      Cont R I barRead ->
        Cont barRead C rootRead ->
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row B ∨ hsame row L ∨ hsame row R ∨ hsame row I ∨
                  hsame row rootRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont R I barRead ∧ Cont barRead C rootRead)
              hsame ∧ UnaryHistory barRead ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet barRoute rootRoute
  obtain ⟨_unaryB, _unaryL, _unaryT, _unaryW, unaryR, unaryI, _unaryH, unaryC,
    _routeT, _routeR, _routeN⟩ := packet
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed unaryR unaryI barRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed barUnary unaryC rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row L ∨ hsame row R ∨ hsame row I ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R I barRead ∧ Cont barRead C rootRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
      exact ⟨source.right, barRoute, rootRoute⟩
  }
  exact ⟨cert, barUnary, rootUnary⟩

end BEDC.Derived.FanCompactUp
