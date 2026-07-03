import BEDC.Derived.BetaStepBoundaryUp.TasteGate
import BEDC.Derived.BetaStepBoundaryUp.ObstructionTriggerEnumeration
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BetaStepBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem BetaStepBoundaryScopedObstructionRoute
    {rule conversion obstruction transport route provenance name scopedRead triggerRead : BHist} :
    Cont obstruction route triggerRead →
      Cont triggerRead transport scopedRead →
        SemanticNameCert
            (fun row : BHist =>
              hsame row scopedRead ∧
                hsame row (BEDC.FKernel.Cont.append triggerRead transport))
            (fun row : BHist =>
              hsame row rule ∨ hsame row conversion ∨ hsame row obstruction ∨
                hsame row transport ∨ hsame row route ∨ hsame row triggerRead ∨
                  hsame row scopedRead)
            (fun row : BHist =>
              Cont obstruction route triggerRead ∧ Cont triggerRead transport scopedRead ∧
                hsame row scopedRead)
            hsame := by
  -- BEDC touchpoint anchor: BetaStepBoundaryUp BHist Cont hsame SemanticNameCert
  intro obstructionRoute scopedRoute
  have _provenanceRow : hsame provenance provenance := hsame_refl provenance
  have _nameRow : hsame name name := hsame_refl name
  have scopedExact : hsame scopedRead (BEDC.FKernel.Cont.append triggerRead transport) := by
    cases scopedRoute
    exact hsame_refl _
  exact {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedExact⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨obstructionRoute, scopedRoute, sourceRow.left⟩
  }

theorem BetaStepBoundary_scoped_obstruction_route
    {rule conversion obstruction transport route provenance name triggerRead scopedRead : BHist} :
    Cont obstruction route triggerRead →
      Cont triggerRead transport scopedRead →
        SemanticNameCert
          (fun row : BHist =>
            hsame row scopedRead ∧ hsame row (BEDC.FKernel.Cont.append triggerRead transport))
          (fun row : BHist =>
            hsame row rule ∨ hsame row conversion ∨ hsame row obstruction ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row name ∨ hsame row triggerRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            Cont obstruction route triggerRead ∧ Cont triggerRead transport scopedRead ∧
              hsame row scopedRead)
          hsame := by
  -- BEDC touchpoint anchor: BetaStepBoundaryUp BHist Cont hsame SemanticNameCert
  intro triggerRoute scopedRoute
  have _ruleRow : hsame rule rule := hsame_refl rule
  have _conversionRow : hsame conversion conversion := hsame_refl conversion
  have _obstructionRow : hsame obstruction obstruction := hsame_refl obstruction
  have _transportRow : hsame transport transport := hsame_refl transport
  have _routeRow : hsame route route := hsame_refl route
  have _provenanceRow : hsame provenance provenance := hsame_refl provenance
  have _nameRow : hsame name name := hsame_refl name
  have _triggerRow : hsame triggerRead triggerRead := hsame_refl triggerRead
  have scopedExact : hsame scopedRead (BEDC.FKernel.Cont.append triggerRead transport) := by
    cases scopedRoute
    exact hsame_refl _
  exact {
    core := {
      carrier_inhabited := Exists.intro scopedRead
        ⟨hsame_refl scopedRead, scopedExact⟩
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
            hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨triggerRoute, scopedRoute, source.left⟩
  }

end BEDC.Derived.BetaStepBoundaryUp
