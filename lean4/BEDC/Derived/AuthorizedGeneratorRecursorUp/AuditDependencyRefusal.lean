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

theorem AuthorizedGeneratorRecursorAuditDependencyRefusal [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N auditRead dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont A G auditRead ->
        Cont auditRead N dependencyRead ->
          PkgSig bundle dependencyRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row A ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row A ∧ Cont A G auditRead ∧
                    Cont auditRead N dependencyRead)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧ PkgSig bundle dependencyRead pkg ∧
                    hsame row A)
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier auditRoute dependencyRoute dependencyPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, unaryA, _unaryH,
      _unaryC, carrierPkg, unaryG, unaryN, _carrierBranch, _carrierDescent,
      _carrierOutput, _transportSame, provenancePkg⟩
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryA unaryG auditRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed auditUnary unaryN dependencyRoute
  have sourceAudit : (fun row : BHist => hsame row A ∧ UnaryHistory row) A := by
    exact ⟨hsame_refl A, unaryA⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row A ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∧ Cont A G auditRead ∧ Cont auditRead N dependencyRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle dependencyRead pkg ∧ hsame row A)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro A sourceAudit
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, auditRoute, dependencyRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, dependencyPkg, source.left⟩
    }
  exact ⟨cert, auditUnary, dependencyUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
