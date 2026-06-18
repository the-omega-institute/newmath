import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_carrier_source {Z S M R Q H C P N entryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S entryRead ->
        SemanticNameCert
            (fun row : BHist => hsame row entryRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row entryRead ∧ Cont Z S entryRead)
            (fun row : BHist =>
              hsame row entryRead ∧ hsame H (append Z S) ∧ Cont Q H C ∧ Cont C P N)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory entryRead ∧
              hsame H (append Z S) ∧ Cont Z S entryRead ∧ Cont M R Q ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet entryRoute
  obtain ⟨unaryQ, unaryC, unaryN, sameH⟩ :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have entryUnary : UnaryHistory entryRead :=
    unary_cont_closed unaryZ unaryS entryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row entryRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row entryRead ∧ Cont Z S entryRead)
          (fun row : BHist =>
            hsame row entryRead ∧ hsame H (append Z S) ∧ Cont Q H C ∧ Cont C P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro entryRead ⟨hsame_refl entryRead, entryUnary⟩
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
      exact ⟨source.left, entryRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameH, routeC, routeN⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, entryUnary, sameH,
      entryRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
