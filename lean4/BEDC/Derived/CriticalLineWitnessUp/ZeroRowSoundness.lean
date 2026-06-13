import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_row_soundness
    {Z S M R Q H C P N zeroRead realRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zeroRead →
        Cont R Q realRead →
          Cont zeroRead realRead refusalRead →
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                    hsame row zeroRead ∨ hsame row realRead ∨ hsame row refusalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S zeroRead ∧ Cont R Q realRead ∧
                    Cont zeroRead realRead refusalRead ∧ hsame H (append Z S))
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory realRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute realRoute refusalRoute
  obtain ⟨unaryZ, unaryS, _unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed _unaryM unaryR routeQ
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed unaryR unaryQ realRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed zeroUnary realUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row zeroRead ∨ hsame row realRead ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zeroRead ∧ Cont R Q realRead ∧
              Cont zeroRead realRead refusalRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      exact ⟨source.right, zeroRoute, realRoute, refusalRoute, sameH⟩
  }
  exact ⟨cert, zeroUnary, realUnary, refusalUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
