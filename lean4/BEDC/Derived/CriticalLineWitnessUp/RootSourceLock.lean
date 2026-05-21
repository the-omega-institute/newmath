import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_lock
    {Z S M R Q H C P N sourceRead locked : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceRead →
        Cont sourceRead H locked →
          SemanticNameCert
              (fun row : BHist => hsame row locked ∧ UnaryHistory row)
              (fun row : BHist => hsame row locked ∧ Cont Z S sourceRead)
              (fun row : BHist => hsame row locked ∧ Cont sourceRead H locked)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory sourceRead ∧ UnaryHistory locked ∧ hsame H (append Z S) ∧
                Cont Z S sourceRead ∧ Cont sourceRead H locked ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute lockRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have sourceSameH : hsame sourceRead H :=
    hsame_trans sourceRoute (hsame_symm sameH)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary sourceSameH
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed sourceUnary unaryH lockRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locked ∧ UnaryHistory row)
          (fun row : BHist => hsame row locked ∧ Cont Z S sourceRead)
          (fun row : BHist => hsame row locked ∧ Cont sourceRead H locked)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locked ⟨hsame_refl locked, lockedUnary⟩
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
      exact ⟨source.left, sourceRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, lockRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, sourceUnary, lockedUnary, sameH,
      sourceRoute, lockRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
