import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_normalization_interface
    {Z S M R Q H C P N sourceRead sourceNormal : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead M sourceNormal ->
          SemanticNameCert
              (fun row : BHist => hsame row sourceNormal ∧ UnaryHistory row)
              (fun row : BHist => hsame row sourceNormal ∧ Cont Z S sourceRead)
              (fun row : BHist => hsame row sourceNormal ∧ Cont sourceRead M sourceNormal)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory sourceRead ∧
              UnaryHistory sourceNormal ∧ hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                Cont sourceRead M sourceNormal ∧ Cont M R Q ∧ Cont Q H C ∧
                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute normalRoute
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have normalUnary : UnaryHistory sourceNormal :=
    unary_cont_closed sourceUnary unaryM normalRoute
  have sourceAtNormal :
      (fun row : BHist => hsame row sourceNormal ∧ UnaryHistory row) sourceNormal := by
    exact ⟨hsame_refl sourceNormal, normalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceNormal ∧ UnaryHistory row)
          (fun row : BHist => hsame row sourceNormal ∧ Cont Z S sourceRead)
          (fun row : BHist => hsame row sourceNormal ∧ Cont sourceRead M sourceNormal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceNormal sourceAtNormal
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
      exact ⟨source.left, normalRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, sourceUnary, normalUnary, sameH, sourceRoute,
      normalRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_source_normalization_lock
    {Z S M R Q H C P N sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        SemanticNameCert
            (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row sourceRead)
            (fun row : BHist => hsame row sourceRead ∧ Cont Z S sourceRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory sourceRead ∧
            hsame H (append Z S) ∧ Cont Z S sourceRead ∧ Cont M R Q ∧
              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have sourceAtRead :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row sourceRead)
          (fun row : BHist => hsame row sourceRead ∧ Cont Z S sourceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceAtRead
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
      exact ⟨source.left, sourceRoute⟩
  }
  exact ⟨cert, unaryZ, unaryS, sourceUnary, sameH, sourceRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
