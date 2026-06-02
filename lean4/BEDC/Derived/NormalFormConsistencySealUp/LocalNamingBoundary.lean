import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealLocalNamingBoundary
    {T F N K X H C P L closedRead localRead : BHist} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory L →
                      Cont T F closedRead →
                        Cont P L localRead →
                          hsame localRead closedRead →
                            SemanticNameCert
                                (fun row : BHist =>
                                  hsame row localRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row F ∨ hsame row N ∨
                                    hsame row K ∨ hsame row X ∨ hsame row localRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ hsame row localRead)
                                hsame ∧
                              UnaryHistory closedRead ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary _nUnary _kUnary _xUnary _hUnary _cUnary pUnary lUnary
    closedRoute localRoute _sameLocalClosed
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed tUnary fUnary closedRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed pUnary lUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨
              hsame row X ∨ hsame row localRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row localRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, source.left⟩
  }
  exact ⟨cert, closedUnary, localUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
