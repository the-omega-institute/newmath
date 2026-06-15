import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zeta_strip_source_lock
    {Z S M R Q H C P N zetaRead sourceRead modulusRead sourceLock : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H sourceRead ->
          Cont sourceRead Q modulusRead ->
            Cont modulusRead C sourceLock ->
              SemanticNameCert
                  (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row Q ∨
                      hsame row C ∨ hsame row sourceLock)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont zetaRead H sourceRead ∧
                      Cont sourceRead Q modulusRead ∧ Cont modulusRead C sourceLock)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                  UnaryHistory C ∧ UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory sourceLock ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute sourceRoute modulusRoute sourceLockRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed (unary_cont_closed unaryZ unaryS zetaRoute) unaryH sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary unaryQ modulusRoute
  have sourceLockUnary : UnaryHistory sourceLock :=
    unary_cont_closed modulusUnary unaryC sourceLockRoute
  have sourceAtLock : hsame sourceLock sourceLock ∧ UnaryHistory sourceLock :=
    ⟨hsame_refl sourceLock, sourceLockUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row Q ∨ hsame row C ∨
              hsame row sourceLock)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont zetaRead H sourceRead ∧
              Cont sourceRead Q modulusRead ∧ Cont modulusRead C sourceLock)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceLock sourceAtLock
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zetaRoute, sourceRoute, modulusRoute, sourceLockRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, unaryC, sourceUnary, modulusUnary,
      sourceLockUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
