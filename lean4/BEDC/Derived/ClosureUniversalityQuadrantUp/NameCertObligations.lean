import BEDC.Derived.ClosureUniversalityQuadrantUp.AxisIndependence
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosureUniversalityQuadrantUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ClosureUniversalityQuadrantCarrier_namecert_obligations
    {U D G S A H N substrateRead anchorRead namedRead : BHist} :
    UnaryHistory U →
      UnaryHistory D →
        UnaryHistory S →
          UnaryHistory A →
            UnaryHistory H →
              UnaryHistory N →
                Cont U D G →
                  Cont G S substrateRead →
                    Cont substrateRead A anchorRead →
                      Cont anchorRead N namedRead →
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row U ∨ hsame row D ∨ hsame row G ∨ hsame row S ∨
                                hsame row A ∨ hsame row H ∨ hsame row N ∨
                                  hsame row substrateRead ∨ hsame row anchorRead ∨
                                    hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont U D G ∧ Cont G S substrateRead ∧
                                Cont substrateRead A anchorRead ∧
                                  Cont anchorRead N namedRead)
                            hsame ∧
                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro uUnary dUnary sUnary aUnary _hUnary nUnary axisRoute substrateRoute anchorRoute
    nameRoute
  have tagUnary : UnaryHistory G :=
    unary_cont_closed uUnary dUnary axisRoute
  have substrateUnary : UnaryHistory substrateRead :=
    unary_cont_closed tagUnary sUnary substrateRoute
  have anchorUnary : UnaryHistory anchorRead :=
    unary_cont_closed substrateUnary aUnary anchorRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed anchorUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row D ∨ hsame row G ∨ hsame row S ∨ hsame row A ∨
              hsame row H ∨ hsame row N ∨ hsame row substrateRead ∨
                hsame row anchorRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U D G ∧ Cont G S substrateRead ∧
              Cont substrateRead A anchorRead ∧ Cont anchorRead N namedRead)
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, axisRoute, substrateRoute, anchorRoute, nameRoute⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.ClosureUniversalityQuadrantUp
