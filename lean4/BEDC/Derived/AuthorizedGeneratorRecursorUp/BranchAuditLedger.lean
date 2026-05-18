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

theorem AuthorizedGeneratorRecursorCarrier_branch_audit_ledger [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont branchRead A auditRead ->
          Cont auditRead N publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N
                      bundle pkg ∧ hsame row B)
                  (fun row : BHist =>
                    hsame row B ∧ Cont B D branchRead ∧
                      Cont branchRead A auditRead)
                  (fun _row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg ∧
                      Cont auditRead N publicRead)
                  hsame ∧
                UnaryHistory B ∧ UnaryHistory A ∧ UnaryHistory branchRead ∧
                  UnaryHistory auditRead ∧ UnaryHistory publicRead ∧
                    Cont B D branchRead ∧ Cont branchRead A auditRead ∧
                      Cont auditRead N publicRead ∧ hsame H (append A C) ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier branchRoute auditRoute publicRoute publicPkg
  have carrierPacket :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg :=
    carrier
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, _unaryO, unaryA,
      _unaryH, _unaryC, _unaryP, _unaryG, unaryN, _contIEM, _contMBD,
      _contDOA, sameLedger, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed branchUnary unaryA auditRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary unaryN publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
              hsame row B)
          (fun row : BHist =>
            hsame row B ∧ Cont B D branchRead ∧ Cont branchRead A auditRead)
          (fun _row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg ∧
              Cont auditRead N publicRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro B ⟨carrierPacket, hsame_refl B⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, branchRoute, auditRoute⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, publicPkg, publicRoute⟩
    }
  exact
    ⟨cert, unaryB, unaryA, branchUnary, auditUnary, publicUnary, branchRoute,
      auditRoute, publicRoute, sameLedger, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
