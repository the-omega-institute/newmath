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

theorem AuthorizedGeneratorRecursorRootAuditMembraneSourceRefusal [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N auditRead sourceRead membraneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A auditRead →
        Cont auditRead G sourceRead →
          Cont sourceRead N membraneRead →
            PkgSig bundle membraneRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                      hsame row membraneRead)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row G ∨ hsame row N ∨ hsame row membraneRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle membraneRead pkg ∧
                      hsame row membraneRead)
                  hsame ∧
                UnaryHistory auditRead ∧ UnaryHistory sourceRead ∧ UnaryHistory membraneRead ∧
                  Cont O A auditRead ∧ Cont auditRead G sourceRead ∧
                    Cont sourceRead N membraneRead ∧ hsame H (append A C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle membraneRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier auditRoute sourceRoute membraneRoute membranePkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
      unaryG, unaryN, contIEM, contMBD, contDOA, transportSame, provenancePkg⟩
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryO unaryA auditRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed auditReadUnary unaryG sourceRoute
  have membraneReadUnary : UnaryHistory membraneRead :=
    unary_cont_closed sourceReadUnary unaryN membraneRoute
  have carrierCopy :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
        unaryG, unaryN, contIEM, contMBD, contDOA, transportSame, provenancePkg⟩
  have sourceMembrane :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row membraneRead) membraneRead := by
    exact ⟨carrierCopy, hsame_refl membraneRead⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
            hsame row membraneRead)
        (fun row : BHist =>
          hsame row A ∨ hsame row G ∨ hsame row N ∨ hsame row membraneRead)
        (fun row : BHist =>
          PkgSig bundle P pkg ∧ PkgSig bundle membraneRead pkg ∧
            hsame row membraneRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro membraneRead sourceMembrane
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
      exact Or.inr (Or.inr (Or.inr source.right))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, membranePkg, source.right⟩
  }
  exact
    ⟨cert, auditReadUnary, sourceReadUnary, membraneReadUnary, auditRoute, sourceRoute,
      membraneRoute, transportSame, provenancePkg, membranePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
