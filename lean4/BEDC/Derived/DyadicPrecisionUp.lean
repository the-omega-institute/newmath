import BEDC.Derived.DyadicPrecisionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def DyadicPrecisionSchedule
    (precision radius window transport provenance nameCert ledger : BHist) : Prop :=
  UnaryHistory precision ∧
    UnaryHistory radius ∧
      UnaryHistory window ∧
        UnaryHistory nameCert ∧
          Cont radius nameCert provenance ∧
            Cont precision window transport ∧
              Cont transport provenance ledger

theorem DyadicPrecisionSchedule_common_window_readback
    {precision radius window transport provenance nameCert ledger precision' radius' window'
      transport' provenance' nameCert' ledger' : BHist} :
    DyadicPrecisionSchedule precision radius window transport provenance nameCert ledger →
      DyadicPrecisionSchedule precision' radius' window' transport' provenance' nameCert'
        ledger' →
        hsame precision precision' →
          hsame window window' →
            hsame provenance provenance' →
              Cont precision' window' transport' →
                Cont transport' provenance' ledger' →
                  hsame transport transport' ∧ hsame ledger ledger' := by
  intro left _right samePrecision sameWindow sameProvenance rightTransport rightLedger
  have leftTransport : Cont precision window transport :=
    left.right.right.right.right.right.left
  have leftLedger : Cont transport provenance ledger :=
    left.right.right.right.right.right.right
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame samePrecision sameWindow leftTransport rightTransport
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTransport sameProvenance leftLedger rightLedger
  exact And.intro sameTransport sameLedger

theorem DyadicPrecisionUp_semantic_name_certificate (x : DyadicPrecisionUp) :
    SemanticNameCert
      (fun row : BHist =>
        match x with
        | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
            hsame row precision ∨ hsame row radius ∨ hsame row window ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row nameCert ∨
                hsame row ledger)
      (fun row : BHist =>
        match x with
        | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
            hsame row precision ∨ hsame row radius ∨ hsame row window ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row nameCert ∨
                hsame row ledger)
      (fun row : BHist =>
        match x with
        | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
            hsame row precision ∨ hsame row radius ∨ hsame row window ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row nameCert ∨
                hsame row ledger)
      hsame := by
  cases x with
  | mk precision radius window transport provenance nameCert ledger =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro precision (Or.inl (hsame_refl precision))
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row row' sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro row row' row'' sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row row' sameRows source
            cases source with
            | inl samePrecision =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) samePrecision)
            | inr source =>
                cases source with
                | inl sameRadius =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRadius))
                | inr source =>
                    cases source with
                    | inl sameWindow =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)))
                    | inr source =>
                        cases source with
                        | inl sameTransport =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameTransport))))
                        | inr source =>
                            cases source with
                            | inl sameProvenance =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans
                                            (hsame_symm sameRows) sameProvenance)))))
                            | inr source =>
                                cases source with
                                | inl sameNameCert =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans
                                                  (hsame_symm sameRows) sameNameCert))))))
                                | inr sameLedger =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (hsame_trans
                                                  (hsame_symm sameRows) sameLedger))))))
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.DyadicPrecisionUp
