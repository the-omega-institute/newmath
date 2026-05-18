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

theorem AuthorizedGeneratorRecursorOperationalMembraneAuditHandoff [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditBoundary membraneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead G auditBoundary ->
          Cont A N membraneRead ->
            PkgSig bundle membraneRead pkg ->
              SemanticNameCert (fun row : BHist => hsame row A ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∧ Cont O A outputRead ∧
                      Cont outputRead G auditBoundary ∧ Cont A N membraneRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle membraneRead pkg ∧ hsame row A)
                  hsame ∧
                UnaryHistory auditBoundary ∧ UnaryHistory membraneRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputRoute auditBoundaryRoute membraneRoute membranePkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      _unaryC, provenancePkg, unaryG, unaryN, _carrierSignature, _carrierDescent,
      _carrierAudit, _transportSame, provenancePkgSig⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditBoundaryUnary : UnaryHistory auditBoundary :=
    unary_cont_closed outputUnary unaryG auditBoundaryRoute
  have membraneUnary : UnaryHistory membraneRead :=
    unary_cont_closed unaryA unaryN membraneRoute
  have sourceAudit : (fun row : BHist => hsame row A ∧ UnaryHistory row) A := by
    exact ⟨hsame_refl A, unaryA⟩
  have cert :
      SemanticNameCert (fun row : BHist => hsame row A ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∧ Cont O A outputRead ∧
              Cont outputRead G auditBoundary ∧ Cont A N membraneRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle membraneRead pkg ∧ hsame row A)
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
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, outputRoute, auditBoundaryRoute, membraneRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkgSig, membranePkg, source.left⟩
    }
  exact ⟨cert, auditBoundaryUnary, membraneUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
