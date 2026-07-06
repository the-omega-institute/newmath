import BEDC.Derived.ClosedSubstitutionSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedSubstitutionSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedSubstitutionSealObligationRows [AskSetup] [PackageSetup]
    {Q L M A K substitutionRead shiftRead auditRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q →
      UnaryHistory L →
        UnaryHistory M →
          UnaryHistory A →
            UnaryHistory K →
              Cont Q L substitutionRead →
                Cont substitutionRead M shiftRead →
                  Cont shiftRead A auditRead →
                    Cont auditRead K handoffRead →
                      PkgSig bundle handoffRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row L ∨ hsame row M ∨ hsame row A ∨
                                hsame row auditRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont Q L substitutionRead ∧
                                Cont substitutionRead M shiftRead ∧
                                  Cont shiftRead A auditRead)
                            hsame ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row L ∨ hsame row M ∨ hsame row A ∨
                                hsame row K ∨ hsame row handoffRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont Q L substitutionRead ∧
                                Cont substitutionRead M shiftRead ∧ Cont shiftRead A auditRead ∧
                                  Cont auditRead K handoffRead ∧
                                    PkgSig bundle handoffRead pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro qUnary lUnary mUnary aUnary kUnary qToL subToM shiftToA auditToK handoffPkg
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed qUnary lUnary qToL
  have shiftUnary : UnaryHistory shiftRead :=
    unary_cont_closed substitutionUnary mUnary subToM
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed shiftUnary aUnary shiftToA
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed auditUnary kUnary auditToK
  have auditCert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row L ∨ hsame row M ∨ hsame row A ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q L substitutionRead ∧
              Cont substitutionRead M shiftRead ∧ Cont shiftRead A auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, qToL, subToM, shiftToA⟩
  }
  have handoffCert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row L ∨ hsame row M ∨ hsame row A ∨ hsame row K ∨
              hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q L substitutionRead ∧
              Cont substitutionRead M shiftRead ∧ Cont shiftRead A auditRead ∧
                Cont auditRead K handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, qToL, subToM, shiftToA, auditToK, handoffPkg⟩
  }
  exact ⟨auditCert, handoffCert⟩

end BEDC.Derived.ClosedSubstitutionSealUp
