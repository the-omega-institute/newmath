import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirichletUniformTestUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DirichletUniformTestCarrier_uniform_cauchy_handoff
    {A B S T M C H R P N tailRead boundRead : BHist} :
    UnaryHistory A ->
      UnaryHistory B ->
        UnaryHistory S ->
          Cont A S tailRead ->
            Cont tailRead B boundRead ->
              SemanticNameCert
                (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row tailRead ∨ hsame row boundRead ∨ hsame row A ∨ hsame row B ∨
                    hsame row S ∨ hsame row T ∨ hsame row M ∨ hsame row C ∨
                      hsame row H ∨ hsame row R ∨ hsame row P ∨ hsame row N)
                (fun row : BHist =>
                  (hsame row tailRead ∨ hsame row boundRead) ∧ Cont A S tailRead ∧
                    Cont tailRead B boundRead)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro hA hB hS hTail hBound
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed hA hS hTail
  exact {
    core := {
      carrier_inhabited := Exists.intro tailRead ⟨hsame_refl tailRead, tailUnary⟩
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨Or.inl source.left, hTail, hBound⟩
  }

theorem DirichletUniformTestCarrier_namecert_obligations
    {S B A V W U R E H C P N tailRead readbackRead sealRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory B ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont S W tailRead ->
                Cont tailRead B U ->
                  Cont U R readbackRead ->
                    Cont readbackRead E sealRead ->
                      SemanticNameCert
                        (fun row : BHist => hsame row U ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row B ∨ hsame row A ∨ hsame row V ∨
                            hsame row W ∨ hsame row U ∨ hsame row R ∨ hsame row E ∨
                              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
                        (fun row : BHist =>
                          (hsame row U ∨ hsame row readbackRead ∨ hsame row sealRead) ∧
                            Cont S W tailRead ∧ Cont tailRead B U ∧
                              Cont U R readbackRead ∧ Cont readbackRead E sealRead)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro sourceUnary windowUnary boundUnary readbackUnary sealUnary sourceWindowTail
    tailBoundUniform uniformReadback readbackSeal
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindowTail
  have uniformUnary : UnaryHistory U :=
    unary_cont_closed tailUnary boundUnary tailBoundUniform
  exact {
    core := {
      carrier_inhabited := Exists.intro U ⟨hsame_refl U, uniformUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨Or.inl source.left, sourceWindowTail, tailBoundUniform, uniformReadback,
          readbackSeal⟩
  }

end BEDC.Derived.DirichletUniformTestUp
