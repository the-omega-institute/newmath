import BEDC.Derived.KernelAuditWitnessUp.TasteGate

namespace BEDC.Derived.KernelAuditWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KernelAuditWitnessAcceptanceGate {G A L R H C P N : BHist}
    (candidateRoute : Cont G A C)
    (ledgerRoute : Cont A L C)
    (ancestryRoute : Cont L R C)
    (nameBindsGenerator : hsame N G) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧
            ∃ packet : KernelAuditWitnessUp,
              packet = KernelAuditWitnessUp.mk G A L R H C P N)
        (fun row : BHist =>
          Cont G A C ∧ Cont A L C ∧ Cont L R C ∧ hsame row N)
        (fun row : BHist =>
          hsame row G ∧ hsame A A ∧ hsame L L ∧ hsame R R ∧ hsame C C)
        hsame ∧
      ∃ packet : KernelAuditWitnessUp, packet = KernelAuditWitnessUp.mk G A L R H C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have packetWitness :
      ∃ packet : KernelAuditWitnessUp, packet = KernelAuditWitnessUp.mk G A L R H C P N :=
    Exists.intro (KernelAuditWitnessUp.mk G A L R H C P N) rfl
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              ∃ packet : KernelAuditWitnessUp,
                packet = KernelAuditWitnessUp.mk G A L R H C P N)
          (fun row : BHist =>
            Cont G A C ∧ Cont A L C ∧ Cont L R C ∧ hsame row N)
          (fun row : BHist =>
            hsame row G ∧ hsame A A ∧ hsame L L ∧ hsame R R ∧ hsame C C)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro N ⟨hsame_refl N, packetWitness⟩
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
        intro _row sourceRow
        exact
          ⟨hsame_trans sourceRow.left nameBindsGenerator, hsame_refl A, hsame_refl L,
            hsame_refl R, hsame_refl C⟩
    }
  exact ⟨cert, packetWitness⟩

end BEDC.Derived.KernelAuditWitnessUp
