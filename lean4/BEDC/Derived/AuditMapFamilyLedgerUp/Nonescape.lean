import BEDC.Derived.AuditMapFamilyLedgerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.AuditMapFamilyLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem AuditMapFamilyLedgerCarrier_nonescape [AskSetup] [PackageSetup]
    {G A E P O U B H C L K N read : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    Cont G A E ->
      Cont E P O ->
        Cont O U B ->
          Cont B H C ->
            Cont C L K ->
              Cont K N read ->
                PkgSig bundle read pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row read)
                    (fun row : BHist =>
                      hsame row G ∨ hsame row A ∨ hsame row E ∨ hsame row P ∨
                        hsame row O ∨ hsame row U ∨ hsame row B ∨ hsame row H ∨
                          hsame row C ∨ hsame row L ∨ hsame row K ∨ hsame row N ∨
                            hsame row read)
                    (fun row : BHist =>
                      hsame row read ∧ Cont G A E ∧ Cont E P O ∧ Cont O U B ∧
                        Cont B H C ∧ Cont C L K ∧ Cont K N read ∧
                          PkgSig bundle read pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro familyRoute positiveRoute obstructionRoute transportRoute ledgerRoute readRoute readPkg
  exact {
    core := {
      carrier_inhabited := Exists.intro read (hsame_refl read)
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
        exact hsame_trans (hsame_symm sameRows) source
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source, familyRoute, positiveRoute, obstructionRoute, transportRoute,
          ledgerRoute, readRoute, readPkg⟩
  }

end BEDC.Derived.AuditMapFamilyLedgerUp
