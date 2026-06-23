import BEDC.Derived.EffectivePolishSpaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.EffectivePolishSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem EffectivePolishSpaceRealizerHandoff
    {P D Q S R M L H C G N denseRead streamRead cauchyRead readbackRead sealRead
      namedRead : BHist} :
    UnaryHistory D ->
      UnaryHistory S ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory M ->
              UnaryHistory L ->
                UnaryHistory N ->
                  Cont D S denseRead ->
                    Cont denseRead Q cauchyRead ->
                      Cont cauchyRead R readbackRead ->
                        Cont readbackRead M sealRead ->
                          Cont sealRead N namedRead ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row P ∨ hsame row D ∨ hsame row Q ∨
                                    hsame row S ∨ hsame row R ∨ hsame row M ∨
                                      hsame row L ∨ hsame row H ∨ hsame row C ∨
                                        hsame row G ∨ hsame row N ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont D S denseRead ∧
                                    Cont denseRead Q cauchyRead ∧
                                      Cont cauchyRead R readbackRead ∧
                                        Cont readbackRead M sealRead ∧
                                          Cont sealRead N namedRead)
                                hsame ∧
                              UnaryHistory denseRead ∧ UnaryHistory cauchyRead ∧
                                UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: EffectivePolishSpaceUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro dUnary sUnary qUnary rUnary mUnary _lUnary nUnary denseRoute cauchyRoute
    readbackRoute sealRoute namedRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed dUnary sUnary denseRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed denseUnary qUnary cauchyRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary mUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row D ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨
              hsame row M ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row G ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S denseRead ∧ Cont denseRead Q cauchyRead ∧
              Cont cauchyRead R readbackRead ∧ Cont readbackRead M sealRead ∧
                Cont sealRead N namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, cauchyRoute, readbackRoute, sealRoute, namedRoute⟩
  }
  exact ⟨cert, denseUnary, cauchyUnary, readbackUnary, sealUnary, namedUnary⟩

end BEDC.Derived.EffectivePolishSpaceUp
