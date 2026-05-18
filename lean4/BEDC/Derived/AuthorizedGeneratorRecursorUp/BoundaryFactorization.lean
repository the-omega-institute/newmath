import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.Sig

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBoundaryFactorization [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead auditRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont branchRead A auditRead ->
          Cont auditRead G boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory H ∧
                UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory G ∧ UnaryHistory N ∧
                  UnaryHistory branchRead ∧ UnaryHistory auditRead ∧
                    UnaryHistory boundaryRead ∧ hsame H (append A C) ∧
                      Cont B D branchRead ∧ Cont branchRead A auditRead ∧
                        Cont auditRead G boundaryRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier branchRoute auditRoute boundaryRoute boundaryPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, branchUnary, descentUnary, _unaryO, auditUnary,
      transportUnary, continuationUnary, provenanceUnary, boundaryUnary, localNameUnary,
      _signatureMotive, _motiveDescent, _descentAudit, transportSame, provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed branchReadUnary auditUnary auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed auditReadUnary boundaryUnary boundaryRoute
  exact
    ⟨branchUnary, descentUnary, auditUnary, transportUnary, continuationUnary,
      provenanceUnary, boundaryUnary, localNameUnary, branchReadUnary, auditReadUnary,
      boundaryReadUnary, transportSame, branchRoute, auditRoute, boundaryRoute,
      provenancePkg, boundaryPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
