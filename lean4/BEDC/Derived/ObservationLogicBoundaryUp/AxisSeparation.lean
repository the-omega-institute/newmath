import BEDC.Derived.ObservationLogicBoundaryUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ObservationLogicBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObservationLogicBoundaryAxis_separation [AskSetup] [PackageSetup]
    {O L M K G R H C P N proofRead phaseRead auditRead residueRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory O →
      UnaryHistory L →
        UnaryHistory M →
          UnaryHistory K →
            UnaryHistory G →
              UnaryHistory R →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont O L proofRead →
                          Cont proofRead M phaseRead →
                            Cont phaseRead K auditRead →
                              Cont auditRead G residueRead →
                                Cont residueRead R H →
                                  Cont H C namedRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row O ∨ hsame row L ∨ hsame row M ∨
                                                hsame row K ∨ hsame row G ∨ hsame row R ∨
                                                  hsame row proofRead ∨
                                                    hsame row phaseRead ∨
                                                      hsame row auditRead ∨
                                                        hsame row residueRead ∨
                                                          hsame row namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont O L proofRead ∧
                                                Cont proofRead M phaseRead ∧
                                                  Cont phaseRead K auditRead ∧
                                                    Cont auditRead G residueRead ∧
                                                      PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory proofRead ∧
                                            UnaryHistory phaseRead ∧ UnaryHistory auditRead ∧
                                              UnaryHistory residueRead := by
  -- BEDC touchpoint anchor: ObservationLogicBoundaryUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro oUnary lUnary mUnary kUnary gUnary _rUnary _hUnary _cUnary _pUnary _nUnary
  intro oToL proofToM phaseToK auditToG _residueToR hToC _pPkg nPkg
  have proofUnary : UnaryHistory proofRead :=
    unary_cont_closed oUnary lUnary oToL
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed proofUnary mUnary proofToM
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed phaseUnary kUnary phaseToK
  have residueUnary : UnaryHistory residueRead :=
    unary_cont_closed auditUnary gUnary auditToG
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed _hUnary _cUnary hToC
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row L ∨ hsame row M ∨ hsame row K ∨ hsame row G ∨
              hsame row R ∨ hsame row proofRead ∨ hsame row phaseRead ∨
                hsame row auditRead ∨ hsame row residueRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O L proofRead ∧ Cont proofRead M phaseRead ∧
              Cont phaseRead K auditRead ∧ Cont auditRead G residueRead ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      repeat (first | exact sourceRow.left | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, oToL, proofToM, phaseToK, auditToG, nPkg⟩
  }
  exact ⟨cert, proofUnary, phaseUnary, auditUnary, residueUnary⟩

end BEDC.Derived.ObservationLogicBoundaryUp
