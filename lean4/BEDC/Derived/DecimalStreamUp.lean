import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DecimalStreamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def DecimalStreamCarrier (E S W L Q R A H C P N : BHist) : Prop :=
  UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory L ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ Cont W L Q ∧ Cont Q R A ∧
      Cont C P N

theorem DecimalStreamCarrier_namecert_obligations
    {E S W L Q R A H C P N readback : BHist} :
    DecimalStreamCarrier E S W L Q R A H C P N ->
      Cont A C readback ->
        SemanticNameCert
            (fun row : BHist => hsame row readback ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row E ∨ hsame row S ∨ hsame row W ∨ hsame row L ∨
                hsame row Q ∨ hsame row R ∨ hsame row A ∨ hsame row readback)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont A C readback ∧ Cont W L Q ∧ Cont Q R A)
            hsame ∧ UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet readbackRoute
  obtain ⟨_unaryE, _unaryS, unaryW, unaryL, unaryR, _unaryH, unaryC, routeQ,
    routeA, _routeN⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryW unaryL routeQ
  have unaryA : UnaryHistory A :=
    unary_cont_closed unaryQ unaryR routeA
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed unaryA unaryC readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row S ∨ hsame row W ∨ hsame row L ∨
              hsame row Q ∨ hsame row R ∨ hsame row A ∨ hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A C readback ∧ Cont W L Q ∧ Cont Q R A)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback ⟨hsame_refl readback, readbackUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, readbackRoute, routeQ, routeA⟩
  }
  exact ⟨cert, readbackUnary⟩

end BEDC.Derived.DecimalStreamUp
