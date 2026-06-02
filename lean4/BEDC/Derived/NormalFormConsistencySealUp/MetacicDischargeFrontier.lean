import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealMetacicDischargeFrontier [AskSetup] [PackageSetup]
    {T F N K X _H C P L closedNormalRead boundaryRead dischargeRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              UnaryHistory C ->
                UnaryHistory P ->
                  UnaryHistory L ->
                    Cont T F closedNormalRead ->
                      Cont N K boundaryRead ->
                        Cont boundaryRead X dischargeRead ->
                          Cont dischargeRead C namedRead ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row T ∨ hsame row F ∨ hsame row N ∨
                                      hsame row K ∨ hsame row X ∨
                                        hsame row dischargeRead ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont boundaryRead X dischargeRead ∧
                                      PkgSig bundle P pkg)
                                  hsame ∧
                                UnaryHistory closedNormalRead ∧
                                  UnaryHistory boundaryRead ∧
                                    UnaryHistory dischargeRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro tUnary fUnary nUnary kUnary xUnary cUnary _pUnary _lUnary closedNormalRoute
    boundaryRoute dischargeRoute namedRoute pkgSig
  have closedNormalUnary : UnaryHistory closedNormalRead :=
    unary_cont_closed tUnary fUnary closedNormalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed nUnary kUnary boundaryRoute
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed boundaryUnary xUnary dischargeRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed dischargeUnary cUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row dischargeRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundaryRead X dischargeRead ∧ PkgSig bundle P pkg)
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, dischargeRoute, pkgSig⟩
  }
  exact ⟨cert, closedNormalUnary, boundaryUnary, dischargeUnary, namedUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
