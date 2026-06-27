import BEDC.Derived.RegularCauchyMinUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyMinSelector_ledger_exactness
    {A B W DA DB J S R E H C P N aSelected bSelected : BHist} :
    UnaryHistory A ->
      UnaryHistory B ->
        UnaryHistory W ->
          UnaryHistory DA ->
            UnaryHistory DB ->
              UnaryHistory S ->
                Cont A W aSelected ->
                  Cont aSelected DA S ->
                    Cont B W bSelected ->
                      Cont bSelected DB S ->
                        SemanticNameCert
                            (fun row : BHist => hsame row S ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                                hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                                  hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                                    hsame row N)
                            (fun row : BHist =>
                              UnaryHistory row ∧
                                ((Cont A W aSelected ∧ Cont aSelected DA S) ∨
                                  (Cont B W bSelected ∧ Cont bSelected DB S)))
                            hsame ∧
                          UnaryHistory aSelected ∧ UnaryHistory bSelected ∧
                            UnaryHistory S := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro aUnary bUnary wUnary daUnary dbUnary sUnary aRoute aSelect bRoute bSelect
  have aSelectedUnary : UnaryHistory aSelected :=
    unary_cont_closed aUnary wUnary aRoute
  have bSelectedUnary : UnaryHistory bSelected :=
    unary_cont_closed bUnary wUnary bRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row S ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨ hsame row DB ∨
              hsame row J ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧
              ((Cont A W aSelected ∧ Cont aSelected DA S) ∨
                (Cont B W bSelected ∧ Cont bSelected DB S)))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro S ⟨hsame_refl S, sUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, Or.inl ⟨aRoute, aSelect⟩⟩
  }
  exact ⟨cert, aSelectedUnary, bSelectedUnary, sUnary⟩

end BEDC.Derived.RegularCauchyMinUp
