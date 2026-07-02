import BEDC.Derived.FiniteWindowRealSeparationUp.ScopedKernelRoute

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FiniteWindowRealSeparation_public_route
    {W D S R H C P N windowRead sealRead transportRead provenanceRead
      publicRead : BHist} :
    UnaryHistory W -> UnaryHistory D -> UnaryHistory S -> UnaryHistory R ->
      UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
        Cont W D windowRead -> Cont windowRead S sealRead ->
          Cont sealRead R transportRead -> Cont transportRead H provenanceRead ->
            Cont provenanceRead C publicRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row windowRead ∨ hsame row sealRead ∨
                          hsame row transportRead ∨ hsame row provenanceRead ∨
                            hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W D windowRead ∧
                      Cont windowRead S sealRead ∧ Cont sealRead R transportRead ∧
                        Cont transportRead H provenanceRead ∧
                          Cont provenanceRead C publicRead)
                  hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD unaryS unaryR unaryH unaryC _unaryP _unaryN windowRoute
    sealRoute transportRoute provenanceRoute publicRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryD windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary unaryS sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary unaryR transportRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed transportUnary unaryH provenanceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed provenanceUnary unaryC publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row windowRead ∨
                hsame row sealRead ∨ hsame row transportRead ∨
                  hsame row provenanceRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧ Cont windowRead S sealRead ∧
              Cont sealRead R transportRead ∧ Cont transportRead H provenanceRead ∧
                Cont provenanceRead C publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      right; right; right; right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, sealRoute, transportRoute, provenanceRoute,
          publicRoute⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.FiniteWindowRealSeparationUp
