import BEDC.Derived.RegSeqRatUp.RealTerminalFourFaceExactness

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatFourFaceAuditThresholdFactorization [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace realFace
      terminalRead auditRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg →
      Cont schedule index streamFace →
        Cont endpoint radius dyadicFace →
          Cont regularity provenance realFace →
            Cont realFace readback terminalRead →
              Cont terminalRead realFace auditRead →
                PkgSig bundle realFace pkg →
                  PkgSig bundle terminalRead pkg →
                    PkgSig bundle auditRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row streamFace ∨ hsame row dyadicFace ∨
                              hsame row realFace ∨ hsame row terminalRead ∨
                                hsame row auditRead)
                          (fun row : BHist =>
                            hsame row auditRead ∧ PkgSig bundle auditRead pkg)
                          hsame ∧
                        UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧
                          UnaryHistory realFace ∧ UnaryHistory terminalRead ∧
                            UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier streamRoute dyadicRoute realRoute terminalRoute auditRoute realPkg terminalPkg
    auditPkg
  have pullback :=
    RegSeqRatFourFaceTerminalPullback carrier streamRoute dyadicRoute realRoute terminalRoute
      realPkg terminalPkg
  have streamUnary : UnaryHistory streamFace := pullback.right.right.right.right.left
  have dyadicUnary : UnaryHistory dyadicFace := pullback.right.right.right.right.right.left
  have realUnary : UnaryHistory realFace := pullback.right.right.right.right.right.right.left
  have terminalUnary : UnaryHistory terminalRead :=
    pullback.right.right.right.right.right.right.right.left
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed terminalUnary realUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row streamFace ∨ hsame row dyadicFace ∨ hsame row realFace ∨
              hsame row terminalRead ∨ hsame row auditRead)
          (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead
        ⟨hsame_refl auditRead, auditUnary⟩
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
      exact ⟨source.left, auditPkg⟩
  }
  exact ⟨cert, streamUnary, dyadicUnary, realUnary, terminalUnary, auditUnary⟩

end BEDC.Derived.RegSeqRatUp
