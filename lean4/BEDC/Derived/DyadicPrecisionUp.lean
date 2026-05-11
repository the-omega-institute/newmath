import BEDC.Derived.DyadicPrecisionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

def DyadicPrecisionEmptySchedule [AskSetup] [PackageSetup]
    (radius transport provenance nameRow ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory radius ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
    UnaryHistory nameRow ∧ UnaryHistory ledger ∧ Cont BHist.Empty radius BHist.Empty ∧
      Cont BHist.Empty transport provenance ∧ PkgSig bundle provenance pkg

theorem DyadicPrecisionEmptySchedule_exactness [AskSetup] [PackageSetup]
    {radius transport provenance nameRow ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger bundle pkg ->
      UnaryHistory BHist.Empty ∧ UnaryHistory radius ∧ UnaryHistory transport ∧
        UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory ledger ∧
          Cont BHist.Empty radius BHist.Empty ∧ Cont BHist.Empty transport provenance ∧
            PkgSig bundle provenance pkg ∧
              SemanticNameCert
                (fun row : BHist =>
                  DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
                    bundle pkg ∧ hsame row nameRow)
                (fun row : BHist =>
                  DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
                    bundle pkg ∧ hsame row nameRow)
                (fun row : BHist =>
                  DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
                    bundle pkg ∧ hsame row nameRow)
                hsame := by
  intro schedule
  have schedulePacket := schedule
  obtain ⟨radiusUnary, transportUnary, provenanceUnary, nameUnary, ledgerUnary,
    radiusRow, provenanceRow, pkgRow⟩ := schedule
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
            bundle pkg ∧ hsame row nameRow)
        (fun row : BHist =>
          DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
            bundle pkg ∧ hsame row nameRow)
        (fun row : BHist =>
          DyadicPrecisionEmptySchedule radius transport provenance nameRow ledger
            bundle pkg ∧ hsame row nameRow)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro nameRow (And.intro schedulePacket (hsame_refl nameRow))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨unary_empty, radiusUnary, transportUnary, provenanceUnary, nameUnary, ledgerUnary,
      radiusRow, provenanceRow, pkgRow, semantic⟩

end BEDC.Derived.DyadicPrecisionUp
