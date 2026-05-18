import BEDC.Derived.AspectChainUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AspectChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem AspectChainNameCertObligations (x : AspectChainUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ records inscription gap locality otherMinds transport routes provenance nameCert : BHist,
          x =
              AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
                nameCert ∧
            hsame row nameCert)
      (fun row : BHist =>
        ∃ records inscription gap locality otherMinds transport routes provenance nameCert : BHist,
          x =
              AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
                nameCert ∧
            (hsame row records ∨ hsame row inscription ∨ hsame row gap ∨ hsame row locality ∨
              hsame row otherMinds ∨ hsame row transport ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row nameCert))
      (fun row : BHist =>
        ∃ records inscription gap locality otherMinds transport routes provenance nameCert : BHist,
          x =
              AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
                nameCert ∧
            hsame row nameCert ∧ aspectChainFromEventFlow (aspectChainToEventFlow x) = some x)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert ChapterTasteGate
  cases x with
  | mk records inscription gap locality otherMinds transport routes provenance nameCert =>
      exact {
        core := {
          carrier_inhabited := by
            apply Exists.intro nameCert
            apply Exists.intro records
            apply Exists.intro inscription
            apply Exists.intro gap
            apply Exists.intro locality
            apply Exists.intro otherMinds
            apply Exists.intro transport
            apply Exists.intro routes
            apply Exists.intro provenance
            apply Exists.intro nameCert
            exact And.intro rfl (hsame_refl nameCert)
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row other same
            exact hsame_symm same
          equiv_trans := by
            intro row middle other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other same source
            cases source with
            | intro records0 source =>
                cases source with
                | intro inscription0 source =>
                    cases source with
                    | intro gap0 source =>
                        cases source with
                        | intro locality0 source =>
                            cases source with
                            | intro otherMinds0 source =>
                                cases source with
                                | intro transport0 source =>
                                    cases source with
                                    | intro routes0 source =>
                                        cases source with
                                        | intro provenance0 source =>
                                            cases source with
                                            | intro nameCert0 source =>
                                                cases source with
                                                | intro hx sameName =>
                                                    apply Exists.intro records0
                                                    apply Exists.intro inscription0
                                                    apply Exists.intro gap0
                                                    apply Exists.intro locality0
                                                    apply Exists.intro otherMinds0
                                                    apply Exists.intro transport0
                                                    apply Exists.intro routes0
                                                    apply Exists.intro provenance0
                                                    apply Exists.intro nameCert0
                                                    exact And.intro hx
                                                      (hsame_trans (hsame_symm same) sameName)
        }
        pattern_sound := by
          intro row source
          cases source with
          | intro records0 source =>
              cases source with
              | intro inscription0 source =>
                  cases source with
                  | intro gap0 source =>
                      cases source with
                      | intro locality0 source =>
                          cases source with
                          | intro otherMinds0 source =>
                              cases source with
                              | intro transport0 source =>
                                  cases source with
                                  | intro routes0 source =>
                                      cases source with
                                      | intro provenance0 source =>
                                          cases source with
                                          | intro nameCert0 source =>
                                              cases source with
                                              | intro hx sameName =>
                                                  apply Exists.intro records0
                                                  apply Exists.intro inscription0
                                                  apply Exists.intro gap0
                                                  apply Exists.intro locality0
                                                  apply Exists.intro otherMinds0
                                                  apply Exists.intro transport0
                                                  apply Exists.intro routes0
                                                  apply Exists.intro provenance0
                                                  apply Exists.intro nameCert0
                                                  exact And.intro hx
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr sameName))))))))
        ledger_sound := by
          intro row source
          cases source with
          | intro records0 source =>
              cases source with
              | intro inscription0 source =>
                  cases source with
                  | intro gap0 source =>
                      cases source with
                      | intro locality0 source =>
                          cases source with
                          | intro otherMinds0 source =>
                              cases source with
                              | intro transport0 source =>
                                  cases source with
                                  | intro routes0 source =>
                                      cases source with
                                      | intro provenance0 source =>
                                          cases source with
                                          | intro nameCert0 source =>
                                              cases source with
                                              | intro hx sameName =>
                                                  cases hx
                                                  have roundTrip :=
                                                    aspectChainChapterTasteGate.round_trip
                                                      (AspectChainUp.mk records inscription gap
                                                        locality otherMinds transport routes
                                                        provenance nameCert)
                                                  change
                                                    aspectChainFromEventFlow
                                                        (aspectChainToEventFlow
                                                          (AspectChainUp.mk records inscription gap
                                                            locality otherMinds transport routes
                                                            provenance nameCert)) =
                                                      some
                                                        (AspectChainUp.mk records inscription gap
                                                          locality otherMinds transport routes
                                                          provenance nameCert) at roundTrip
                                                  apply Exists.intro records
                                                  apply Exists.intro inscription
                                                  apply Exists.intro gap
                                                  apply Exists.intro locality
                                                  apply Exists.intro otherMinds
                                                  apply Exists.intro transport
                                                  apply Exists.intro routes
                                                  apply Exists.intro provenance
                                                  apply Exists.intro nameCert
                                                  exact And.intro rfl
                                                    (And.intro sameName roundTrip)
      }

end BEDC.Derived.AspectChainUp
