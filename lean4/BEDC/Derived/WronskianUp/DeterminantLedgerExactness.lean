import BEDC.Derived.WronskianUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem WronskianCarrier_determinant_ledger_exactness
    {F D J Omega S R E : BHist} {_H _C : BHist}
    {P N determinantRead valueRead sealRead : BHist} :
    UnaryHistory F ->
      UnaryHistory D ->
        UnaryHistory J ->
          UnaryHistory Omega ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory E ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont F D J ->
                        Cont J Omega determinantRead ->
                          Cont S R valueRead ->
                            Cont valueRead E sealRead ->
                              Cont sealRead P N ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row F ∨ hsame row D ∨ hsame row J ∨
                                        hsame row Omega ∨ hsame row S ∨ hsame row R ∨
                                          hsame row E ∨ hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont F D J ∧
                                        Cont J Omega determinantRead ∧
                                          Cont S R valueRead ∧
                                            Cont valueRead E sealRead ∧
                                              Cont sealRead P N)
                                    hsame ∧
                                  UnaryHistory determinantRead ∧ UnaryHistory valueRead ∧
                                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro fUnary dUnary jUnary omegaUnary sUnary rUnary eUnary pUnary _nUnary familyRoute
    determinantRoute valueRoute sealRoute nameRoute
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F D J ∧ Cont J Omega determinantRead ∧
              Cont S R valueRead ∧ Cont valueRead E sealRead ∧ Cont sealRead P N)
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, familyRoute, determinantRoute, valueRoute, sealRoute, nameRoute⟩
  }
  exact ⟨cert, determinantUnary, valueUnary, sealUnary⟩

end BEDC.Derived.WronskianUp
