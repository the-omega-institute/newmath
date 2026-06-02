import BEDC.Derived.KernelAuditWitnessUp.TasteGate

namespace BEDC.Derived.KernelAuditWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KernelAuditWitnessKernelScopeBinding {G A L R H C P N : BHist}
    (candidateRoute : Cont G A C)
    (ledgerRoute : Cont A L C)
    (ancestryRoute : Cont L R C) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧
            ∃ packet : KernelAuditWitnessUp,
              packet = KernelAuditWitnessUp.mk G A L R H C P N)
        (fun row : BHist =>
          Cont G A C ∧ Cont A L C ∧ Cont L R C ∧ hsame row N)
        (fun _row : BHist =>
          hsame A A ∧ hsame L L ∧ hsame R R ∧ hsame C C ∧ hsame P P ∧
            hsame N N)
        hsame ∧
      ∃ packet : KernelAuditWitnessUp,
        packet = KernelAuditWitnessUp.mk G A L R H C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro N
            ⟨hsame_refl N,
              Exists.intro (KernelAuditWitnessUp.mk G A L R H C P N) rfl⟩
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
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨candidateRoute, ledgerRoute, ancestryRoute, sourceRow.left⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨hsame_refl A, hsame_refl L, hsame_refl R, hsame_refl C,
            hsame_refl P, hsame_refl N⟩
    }
  · exact Exists.intro (KernelAuditWitnessUp.mk G A L R H C P N) rfl

end BEDC.Derived.KernelAuditWitnessUp
