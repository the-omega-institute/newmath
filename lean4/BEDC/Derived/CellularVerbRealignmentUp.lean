import BEDC.Derived.CellularVerbRealignmentUp.NameCertObligations

namespace BEDC.Derived.CellularVerbRealignmentUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CellularVerbRealignment_non_escape_boundary
    {B O M H E K L C P N markRead histRead extRead contRead namedRead : BHist} :
    UnaryHistory B ->
      UnaryHistory O ->
        UnaryHistory M ->
          UnaryHistory H ->
            UnaryHistory E ->
              UnaryHistory K ->
                UnaryHistory L ->
                  UnaryHistory N ->
                    Cont B O markRead ->
                      Cont markRead M histRead ->
                        Cont histRead E extRead ->
                          Cont extRead K contRead ->
                            Cont contRead N namedRead ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row B ∨ hsame row O ∨ hsame row M ∨
                                      hsame row H ∨ hsame row E ∨ hsame row K ∨
                                        hsame row L ∨ hsame row N ∨ hsame row markRead ∨
                                          hsame row histRead ∨ hsame row extRead ∨
                                            hsame row contRead ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont B O markRead ∧
                                      Cont markRead M histRead ∧ Cont histRead E extRead ∧
                                        Cont extRead K contRead ∧ Cont contRead N namedRead)
                                  hsame ∧
                                UnaryHistory markRead ∧ UnaryHistory histRead ∧
                                  UnaryHistory extRead ∧ UnaryHistory contRead ∧
                                    UnaryHistory namedRead ∧
                                      hsame markRead (append B O) ∧
                                        hsame histRead (append markRead M) ∧
                                          hsame extRead (append histRead E) ∧
                                            hsame contRead (append extRead K) ∧
                                              hsame namedRead (append contRead N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro bUnary oUnary mUnary _hUnary eUnary kUnary _lUnary nUnary markRoute histRoute
    extRoute contRoute namedRoute
  let _cRow : BHist := C
  let _pRow : BHist := P
  have markUnary : UnaryHistory markRead :=
    unary_cont_closed bUnary oUnary markRoute
  have histUnary : UnaryHistory histRead :=
    unary_cont_closed markUnary mUnary histRoute
  have extUnary : UnaryHistory extRead :=
    unary_cont_closed histUnary eUnary extRoute
  have contUnary : UnaryHistory contRead :=
    unary_cont_closed extUnary kUnary contRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed contUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row O ∨ hsame row M ∨ hsame row H ∨
              hsame row E ∨ hsame row K ∨ hsame row L ∨ hsame row N ∨
                hsame row markRead ∨ hsame row histRead ∨ hsame row extRead ∨
                  hsame row contRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B O markRead ∧ Cont markRead M histRead ∧
              Cont histRead E extRead ∧ Cont extRead K contRead ∧ Cont contRead N namedRead)
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, markRoute, histRoute, extRoute, contRoute, namedRoute⟩
  }
  exact
    ⟨cert, markUnary, histUnary, extUnary, contUnary, namedUnary, markRoute, histRoute,
      extRoute, contRoute, namedRoute⟩

end BEDC.Derived.CellularVerbRealignmentUp
