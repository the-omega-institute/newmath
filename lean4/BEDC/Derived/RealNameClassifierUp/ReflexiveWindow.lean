import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RealNameClassifierReflexiveWindow
    {A W D T R H K _P S _N classifierRead sealRead : BHist} :
    UnaryHistory A →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory T →
            UnaryHistory R →
              UnaryHistory S →
                Cont W D classifierRead →
                  Cont classifierRead R sealRead →
                    hsame H K →
                      SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row A ∨ hsame row W ∨ hsame row D ∨ hsame row T ∨
                              hsame row R ∨ hsame row S ∨ hsame row classifierRead ∨
                                hsame row sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont W D classifierRead ∧
                              Cont classifierRead R sealRead ∧ hsame H K)
                          hsame ∧
                        UnaryHistory classifierRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro _aUnary wUnary dUnary _tUnary rUnary _sUnary classifierRoute sealRoute sameHK
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed wUnary dUnary classifierRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierUnary rUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row D ∨ hsame row T ∨ hsame row R ∨
              hsame row S ∨ hsame row classifierRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D classifierRead ∧
              Cont classifierRead R sealRead ∧ hsame H K)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact ⟨source.right, classifierRoute, sealRoute, sameHK⟩
  }
  exact ⟨cert, classifierUnary, sealUnary⟩

end BEDC.Derived.RealNameClassifierUp
