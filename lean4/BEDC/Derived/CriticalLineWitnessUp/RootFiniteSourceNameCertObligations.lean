import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_finite_source_namecert_obligations
    {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      ∃ sourceRead : BHist, ∃ classifierRead : BHist,
        Cont (append Z S) Q sourceRead ∧ Cont sourceRead N classifierRead ∧
          SemanticNameCert
              (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row classifierRead)
              (fun row : BHist => hsame row classifierRead ∧ Cont sourceRead N classifierRead)
              hsame ∧
            UnaryHistory sourceRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet
  let sourceRead : BHist := append (append Z S) Q
  let classifierRead : BHist := append sourceRead N
  have sourceRoute : Cont (append Z S) Q sourceRead := by
    exact cont_intro rfl
  have classifierRoute : Cont sourceRead N classifierRead := by
    exact cont_intro rfl
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryN : UnaryHistory N :=
    routeClosure.right.right.left
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed (unary_cont_closed unaryZ unaryS (cont_intro rfl)) unaryQ sourceRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sourceUnary unaryN classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row classifierRead)
          (fun row : BHist => hsame row classifierRead ∧ Cont sourceRead N classifierRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, classifierRoute⟩
  }
  exact
    ⟨sourceRead, classifierRead, sourceRoute, classifierRoute, cert, sourceUnary,
      classifierUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
