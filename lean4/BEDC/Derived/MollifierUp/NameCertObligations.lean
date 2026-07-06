import BEDC.Derived.MollifierUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MollifierUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MollifierCarrier_namecert_obligations
    {S R N P C H L replayRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory N →
          UnaryHistory P →
            UnaryHistory C →
              UnaryHistory H →
                UnaryHistory L →
                  Cont S R N →
                    Cont N P C →
                      Cont C H replayRead →
                        SemanticNameCert
                            (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row R ∨ hsame row N ∨
                                hsame row P ∨ hsame row C ∨ hsame row H ∨
                                  hsame row L ∨ hsame row replayRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧
                                Cont C H replayRead)
                            hsame ∧
                          UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro sUnary rUnary _nUnary pUnary _cUnary hUnary _lUnary supportRoute
    convolutionRoute replayRoute
  have supportUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have convolutionUnary : UnaryHistory C :=
    unary_cont_closed supportUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed convolutionUnary hUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨ hsame row C ∨
              hsame row H ∨ hsame row L ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧ Cont C H replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
          Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, supportRoute, convolutionRoute, replayRoute⟩
  }
  exact ⟨cert, replayUnary⟩

theorem MollifierCarrier_convolution_regularization_route
    {S R N P C H L replayRead outputRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            UnaryHistory L →
              Cont S R N →
                Cont N P C →
                  Cont C H replayRead →
                    Cont replayRead L outputRead →
                      SemanticNameCert
                          (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row R ∨ hsame row N ∨
                              hsame row P ∨ hsame row C ∨ hsame row H ∨
                                hsame row L ∨ hsame row replayRead ∨
                                  hsame row outputRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧
                              Cont C H replayRead ∧ Cont replayRead L outputRead)
                          hsame ∧
                        UnaryHistory outputRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro sUnary rUnary pUnary hUnary lUnary supportRoute convolutionRoute replayRoute
    outputRoute
  have supportUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have convolutionUnary : UnaryHistory C :=
    unary_cont_closed supportUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed convolutionUnary hUnary replayRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed replayUnary lUnary outputRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row outputRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨ hsame row C ∨
              hsame row H ∨ hsame row L ∨ hsame row replayRead ∨ hsame row outputRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧ Cont C H replayRead ∧
              Cont replayRead L outputRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro outputRead ⟨hsame_refl outputRead, outputUnary⟩
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
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, supportRoute, convolutionRoute, replayRoute, outputRoute⟩
  }
  exact ⟨cert, outputUnary⟩

end BEDC.Derived.MollifierUp
