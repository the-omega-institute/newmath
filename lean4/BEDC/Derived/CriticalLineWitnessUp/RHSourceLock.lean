import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_source_lock
    {Z S M R Q H C P N sourceRead locked rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead H locked ->
          Cont locked C rhRead ->
            SemanticNameCert
                (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row rhRead ∧ Cont Z S sourceRead)
                (fun row : BHist => hsame row rhRead ∧ Cont locked C rhRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                UnaryHistory sourceRead ∧ UnaryHistory locked ∧ UnaryHistory rhRead ∧
                  hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                    Cont sourceRead H locked ∧ Cont locked C rhRead ∧ Cont M R Q ∧
                      Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute lockRoute rhRoute
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
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed lockedUnary (unary_cont_closed unaryQ unaryH routeC) rhRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row rhRead ∧ Cont Z S sourceRead)
          (fun row : BHist => hsame row rhRead ∧ Cont locked C rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead ⟨hsame_refl rhRead, rhUnary⟩
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
      exact ⟨source.left, rhRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, sourceUnary, lockedUnary, rhUnary, sameH,
      sourceRoute, lockRoute, rhRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
