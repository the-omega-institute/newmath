import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_source_totality
    {Z S M R Q H C P N sourceRead localRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead H localRead ->
          SemanticNameCert
              (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row localRead ∧ Cont Z S sourceRead)
              (fun row : BHist => hsame row localRead ∧ Cont sourceRead H localRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory sourceRead ∧
              UnaryHistory localRead ∧ hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                Cont sourceRead H localRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute localRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceBaseUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceBaseUnary (hsame_symm sameH)
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed sourceUnary unaryH localRoute
  have sourceAtLocal : hsame localRead localRead ∧ UnaryHistory localRead :=
    ⟨hsame_refl localRead, localUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row localRead ∧ Cont Z S sourceRead)
          (fun row : BHist => hsame row localRead ∧ Cont sourceRead H localRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead sourceAtLocal
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
      exact ⟨source.left, localRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryH, sourceUnary, localUnary, sameH, sourceRoute,
      localRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
