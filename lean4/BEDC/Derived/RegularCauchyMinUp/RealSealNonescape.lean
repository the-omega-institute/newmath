import BEDC.Derived.RegularCauchyMinUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyMinRealSealNonescape
    {A B W DA DB J S R E H C P N readbackRead sealRead : BHist} :
    UnaryHistory S ->
      UnaryHistory R ->
        UnaryHistory E ->
          Cont S R readbackRead ->
            Cont readbackRead E sealRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                      hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S R readbackRead ∧
                      Cont readbackRead E sealRead)
                  hsame ∧
                UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro sUnary rUnary eUnary readbackRoute sealRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed sUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R readbackRead ∧ Cont readbackRead E sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr sourceRow.left))))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, readbackRoute, sealRoute⟩
  }
  exact ⟨cert, readbackUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyMinUp
