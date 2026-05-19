import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.Derived.ClosedtermsubstitutionboundaryUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootNormalizationBoundary [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead boundaryRead normalizedRead : BHist}
    {source value depth shift substitution closedLedger closedAudit closedRoute closedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
        Cont O A outputRead ->
          Cont outputRead N auditRead ->
            Cont G N boundaryRead ->
              Cont shift substitution closedLedger ->
                Cont substitution depth closedAudit ->
                  Cont closedLedger closedAudit closedRoute ->
                    Cont closedRoute auditRead closedRead ->
                      Cont boundaryRead closedRead normalizedRead ->
                        PkgSig bundle normalizedRead pkg ->
                          UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                            UnaryHistory boundaryRead ∧ UnaryHistory closedLedger ∧
                              UnaryHistory closedAudit ∧ UnaryHistory closedRoute ∧
                                UnaryHistory closedRead ∧ UnaryHistory normalizedRead ∧
                                  Cont O A outputRead ∧ Cont outputRead N auditRead ∧
                                    Cont G N boundaryRead ∧
                                      Cont shift substitution closedLedger ∧
                                        Cont substitution depth closedAudit ∧
                                          Cont closedLedger closedAudit closedRoute ∧
                                            Cont closedRoute auditRead closedRead ∧
                                              Cont boundaryRead closedRead normalizedRead ∧
                                                PkgSig bundle normalizedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier classifier outputRoute auditRoute boundaryRoute closedLedgerRoute
    closedAuditRoute closedRouteRoute closedReadRoute normalizedRoute normalizedPkg
  obtain ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
    _unaryC, _unaryP, unaryG, unaryN, _carrierBranch, _carrierDescent, _carrierOutput,
    _transportSame, _provenancePkg⟩ := carrier
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryN auditRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have closedLedgerUnary : UnaryHistory closedLedger :=
    unary_cont_closed shiftUnary substitutionUnary closedLedgerRoute
  have closedAuditUnary : UnaryHistory closedAudit :=
    unary_cont_closed substitutionUnary depthUnary closedAuditRoute
  have closedRouteUnary : UnaryHistory closedRoute :=
    unary_cont_closed closedLedgerUnary closedAuditUnary closedRouteRoute
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed closedRouteUnary auditUnary closedReadRoute
  have normalizedUnary : UnaryHistory normalizedRead :=
    unary_cont_closed boundaryUnary closedReadUnary normalizedRoute
  exact
    ⟨outputUnary, auditUnary, boundaryUnary, closedLedgerUnary, closedAuditUnary,
      closedRouteUnary, closedReadUnary, normalizedUnary, outputRoute, auditRoute,
      boundaryRoute, closedLedgerRoute, closedAuditRoute, closedRouteRoute, closedReadRoute,
      normalizedRoute, normalizedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
