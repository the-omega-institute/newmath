import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_ground_compiler_authorization
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead auditRead
      compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont M B descentRead ->
          Cont O A outputRead ->
            Cont outputRead C auditRead ->
              Cont auditRead N compilerRead ->
                PkgSig bundle compilerRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row N ∧
                          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N
                            bundle pkg)
                      (fun row : BHist =>
                        hsame row N ∧ Cont I E branchRead ∧ Cont M B descentRead ∧
                          Cont O A outputRead ∧ Cont outputRead C auditRead ∧
                            Cont auditRead N compilerRead)
                      (fun row : BHist =>
                        hsame row N ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle compilerRead pkg)
                      hsame ∧
                    UnaryHistory compilerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier branchRoute descentRoute outputRoute auditRoute compilerRoute compilerPkg
  rcases carrier with
    ⟨iUnary, eUnary, mUnary, bUnary, dUnary, oUnary, aUnary, hUnary, cUnary, pUnary,
      gUnary, nUnary, iem, mbd, doa, hSameAuditContinuation, pPkg⟩
  let carrierPacket :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg :=
    ⟨iUnary, eUnary, mUnary, bUnary, dUnary, oUnary, aUnary, hUnary, cUnary, pUnary,
      gUnary, nUnary, iem, mbd, doa, hSameAuditContinuation, pPkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed iUnary eUnary branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed mUnary bUnary descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed oUnary aUnary outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary cUnary auditRoute
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed auditUnary nUnary compilerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg)
        (fun row : BHist =>
          hsame row N ∧ Cont I E branchRead ∧ Cont M B descentRead ∧
            Cont O A outputRead ∧ Cont outputRead C auditRead ∧
              Cont auditRead N compilerRead)
        (fun row : BHist =>
          hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle compilerRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N (And.intro (hsame_refl N) carrierPacket)
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
          intro _row _row' sameRows source
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
      }
      pattern_sound := by
        intro row source
        exact
          ⟨source.left, branchRoute, descentRoute, outputRoute, auditRoute, compilerRoute⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, pPkg, compilerPkg⟩
    }
  exact ⟨cert, compilerUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
