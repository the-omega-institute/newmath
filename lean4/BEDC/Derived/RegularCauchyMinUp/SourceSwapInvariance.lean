import BEDC.Derived.RegularCauchyMinUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyMinCarrier_source_swap_invariance
    {A B W DA DB J S R E H C P N aSelected bSelected : BHist} :
    UnaryHistory A ->
      UnaryHistory B ->
        UnaryHistory W ->
          UnaryHistory DA ->
            UnaryHistory DB ->
              UnaryHistory S ->
                UnaryHistory R ->
                  UnaryHistory E ->
                    Cont A W aSelected ->
                      Cont aSelected DA S ->
                        Cont B W bSelected ->
                          Cont bSelected DB S ->
                            Cont S R E ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    (hsame row S ∨ hsame row R ∨ hsame row E) ∧
                                      UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row A ∨ hsame row B ∨ hsame row W ∨
                                      hsame row DA ∨ hsame row DB ∨ hsame row J ∨
                                        hsame row S ∨ hsame row R ∨ hsame row E ∨
                                          hsame row H ∨ hsame row C ∨ hsame row P ∨
                                            hsame row N)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      ((Cont A W aSelected ∧ Cont aSelected DA S) ∨
                                        (Cont B W bSelected ∧ Cont bSelected DB S)) ∧
                                        Cont S R E)
                                  hsame ∧
                                UnaryHistory aSelected ∧ UnaryHistory bSelected ∧
                                  UnaryHistory E := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist Cont hsame SemanticNameCert
  intro aUnary bUnary wUnary daUnary dbUnary sUnary rUnary eUnary aRoute aLedger bRoute
    bLedger sealRoute
  have aSelectedUnary : UnaryHistory aSelected :=
    unary_cont_closed aUnary wUnary aRoute
  have bSelectedUnary : UnaryHistory bSelected :=
    unary_cont_closed bUnary wUnary bRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row S ∨ hsame row R ∨ hsame row E) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨ hsame row DB ∨
              hsame row J ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧
              ((Cont A W aSelected ∧ Cont aSelected DA S) ∨
                (Cont B W bSelected ∧ Cont bSelected DB S)) ∧
                Cont S R E)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro S ⟨Or.inl (hsame_refl S), sUnary⟩
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
          | inl sameS =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameS)
          | inr tail =>
              cases tail with
              | inl sameR =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR))
              | inr sameE =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameE))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameS =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inl sameS
      | inr tail =>
          cases tail with
          | inl sameR =>
              exact
                Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                  Or.inr <| Or.inl sameR
          | inr sameE =>
              exact
                Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                  Or.inr <| Or.inr <| Or.inl sameE
    ledger_sound := by
      intro _row source
      exact ⟨source.right, Or.inl ⟨aRoute, aLedger⟩, sealRoute⟩
  }
  exact ⟨cert, aSelectedUnary, bSelectedUnary, eUnary⟩

end BEDC.Derived.RegularCauchyMinUp
