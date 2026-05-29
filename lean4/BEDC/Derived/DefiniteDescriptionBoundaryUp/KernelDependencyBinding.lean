import BEDC.Derived.DefiniteDescriptionBoundaryUp.TasteGate

namespace BEDC.Derived.DefiniteDescriptionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DefiniteDescriptionBoundaryKernelDependencyBinding
    {D E U S H C P N witness boundary stable read named : BHist} :
    Cont D E witness →
      Cont E U boundary →
        Cont U S stable →
          Cont stable N read →
            Cont read P named →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row named ∧
                      ∃ packet : DefiniteDescriptionBoundaryUp,
                        packet = DefiniteDescriptionBoundaryUp.mk D E U S H C P N)
                  (fun row : BHist =>
                    Cont D E witness ∧ Cont E U boundary ∧ Cont U S stable ∧
                      Cont stable N read ∧ Cont read P row)
                  (fun row : BHist =>
                    hsame row named ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N)
                  hsame ∧
                Cont D E witness ∧ Cont E U boundary ∧ Cont U S stable ∧
                  Cont stable N read ∧ Cont read P named := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro descriptionWitness existenceBoundary uniquenessStable stableRead readNamed
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro named
            (And.intro (hsame_refl named)
              (Exists.intro (DefiniteDescriptionBoundaryUp.mk D E U S H C P N) rfl))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact
            And.intro (hsame_trans (hsame_symm sameRows) source.left)
              source.right
      }
      pattern_sound := by
        intro row source
        have readRow : Cont read P row :=
          cont_result_hsame_transport readNamed (hsame_symm source.left)
        exact
          ⟨descriptionWitness, existenceBoundary, uniquenessStable, stableRead, readRow⟩
      ledger_sound := by
        intro row source
        exact
          ⟨source.left, hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N⟩
    }
  · exact
      ⟨descriptionWitness, existenceBoundary, uniquenessStable, stableRead, readNamed⟩

end BEDC.Derived.DefiniteDescriptionBoundaryUp
