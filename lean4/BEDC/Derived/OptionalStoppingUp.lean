import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptionalStoppingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OptionalStoppingCarrier [AskSetup] [PackageSetup]
    (prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prob ∧
    UnaryHistory process ∧
    UnaryHistory stopping ∧
    UnaryHistory bound ∧
    UnaryHistory stoppedValue ∧
    UnaryHistory filtration ∧
    UnaryHistory integrability ∧
    UnaryHistory sameRows ∧
    UnaryHistory route ∧
    UnaryHistory provenance ∧
    UnaryHistory namecert ∧
    UnaryHistory endpoint ∧
    Cont stopping bound stoppedValue ∧
    Cont process filtration integrability ∧
    hsame sameRows (append prob process) ∧
    hsame route (append stopping bound) ∧
    hsame provenance (append stoppedValue integrability) ∧
    hsame endpoint (append stoppedValue integrability) ∧
    hsame namecert endpoint ∧
    PkgSig bundle endpoint pkg

theorem OptionalStoppingCarrier_bounded_stopped_value_readback [AskSetup] [PackageSetup]
    {prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptionalStoppingCarrier prob process stopping bound stoppedValue filtration integrability sameRows
      route provenance namecert endpoint bundle pkg →
      Cont stopping bound stoppedValue ∧
        Cont process filtration integrability ∧
          hsame endpoint (append stoppedValue integrability) ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  cases carrier with
  | intro _probUnary rest =>
      cases rest with
      | intro _processUnary rest =>
          cases rest with
          | intro _stoppingUnary rest =>
              cases rest with
              | intro _boundUnary rest =>
                  cases rest with
                  | intro _stoppedValueUnary rest =>
                      cases rest with
                      | intro _filtrationUnary rest =>
                          cases rest with
                          | intro _integrabilityUnary rest =>
                              cases rest with
                              | intro _sameRowsUnary rest =>
                                  cases rest with
                                  | intro _routeUnary rest =>
                                      cases rest with
                                      | intro _provenanceUnary rest =>
                                          cases rest with
                                          | intro _namecertUnary rest =>
                                              cases rest with
                                              | intro _endpointUnary rest =>
                                                  cases rest with
                                                  | intro stoppedValueReadback rest =>
                                                      cases rest with
                                                      | intro integrabilityReadback rest =>
                                                          cases rest with
                                                          | intro _sameRows rest =>
                                                              cases rest with
                                                              | intro _route rest =>
                                                                  cases rest with
                                                                  | intro _provenance rest =>
                                                                      cases rest with
                                                                      | intro endpointSame rest =>
                                                                          cases rest with
                                                                          | intro _namecertSame pkgSig =>
                                                                              exact And.intro
                                                                                stoppedValueReadback
                                                                                (And.intro
                                                                                  integrabilityReadback
                                                                                  (And.intro
                                                                                    endpointSame
                                                                                    pkgSig))

theorem OptionalStoppingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptionalStoppingCarrier prob process stopping bound stoppedValue filtration integrability sameRows
      route provenance namecert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          OptionalStoppingCarrier prob process stopping bound stoppedValue filtration
            integrability sameRows route provenance namecert endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          OptionalStoppingCarrier prob process stopping bound stoppedValue filtration
            integrability sameRows route provenance namecert endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          OptionalStoppingCarrier prob process stopping bound stoppedValue filtration
            integrability sameRows route provenance namecert endpoint bundle pkg ∧
            hsame row endpoint)
        hsame := by
  -- BEDC touchpoint anchor: BHist OptionalStoppingCarrier hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem OptionalStoppingCarrier_finite_expectation_window [AskSetup] [PackageSetup]
    {prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptionalStoppingCarrier prob process stopping bound stoppedValue filtration integrability sameRows
        route provenance namecert endpoint bundle pkg →
      UnaryHistory prob ∧
        UnaryHistory process ∧
          UnaryHistory stopping ∧
            UnaryHistory bound ∧
              UnaryHistory stoppedValue ∧
                UnaryHistory filtration ∧
                  UnaryHistory integrability ∧
                    Cont stopping bound stoppedValue ∧
                      Cont process filtration integrability ∧
                        hsame provenance (append stoppedValue integrability) ∧
                          hsame endpoint (append stoppedValue integrability) ∧
                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨probUnary, processUnary, stoppingUnary, boundUnary, stoppedValueUnary,
    filtrationUnary, integrabilityUnary, _sameRowsUnary, _routeUnary, _provenanceUnary,
    _namecertUnary, _endpointUnary, stoppedValueReadback, integrabilityReadback, _sameRows,
    _route, provenanceSame, endpointSame, _namecertSame, pkgSig⟩ := carrier
  exact And.intro probUnary
    (And.intro processUnary
      (And.intro stoppingUnary
        (And.intro boundUnary
          (And.intro stoppedValueUnary
            (And.intro filtrationUnary
              (And.intro integrabilityUnary
                (And.intro stoppedValueReadback
                  (And.intro integrabilityReadback
                    (And.intro provenanceSame
                      (And.intro endpointSame pkgSig))))))))))

theorem OptionalStoppingCarrier_no_escape_boundary [AskSetup] [PackageSetup]
    {prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptionalStoppingCarrier prob process stopping bound stoppedValue filtration integrability sameRows
        route provenance namecert endpoint bundle pkg ->
      Cont endpoint namecert publicRead ->
        UnaryHistory bound ∧ UnaryHistory stoppedValue ∧ UnaryHistory integrability ∧
          UnaryHistory publicRead ∧ Cont stopping bound stoppedValue ∧
            Cont process filtration integrability ∧ hsame endpoint (append stoppedValue integrability) ∧
              hsame namecert endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier publicReadRow
  obtain ⟨_probUnary, _processUnary, _stoppingUnary, boundUnary, stoppedValueUnary,
    _filtrationUnary, integrabilityUnary, _sameRowsUnary, _routeUnary, _provenanceUnary,
    namecertUnary, endpointUnary, stoppedValueRow, integrabilityRow, _sameRows, _routeSame,
    _provenanceSame, endpointSame, namecertSame, pkgSig⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary namecertUnary publicReadRow
  exact And.intro boundUnary
    (And.intro stoppedValueUnary
      (And.intro integrabilityUnary
        (And.intro publicReadUnary
          (And.intro stoppedValueRow
            (And.intro integrabilityRow
              (And.intro endpointSame
                (And.intro namecertSame pkgSig)))))))

theorem OptionalStoppingCarrier_scoped_dependency_route [AskSetup] [PackageSetup]
    {prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptionalStoppingCarrier prob process stopping bound stoppedValue filtration integrability sameRows
        route provenance namecert endpoint bundle pkg ->
      Cont endpoint route dependencyRead ->
        UnaryHistory prob ∧ UnaryHistory process ∧ UnaryHistory stopping ∧ UnaryHistory bound ∧
          UnaryHistory stoppedValue ∧ UnaryHistory filtration ∧ UnaryHistory integrability ∧
            UnaryHistory dependencyRead ∧ Cont stopping bound stoppedValue ∧
              Cont process filtration integrability ∧ hsame route (append stopping bound) ∧
                hsame endpoint (append stoppedValue integrability) ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier dependencyRoute
  obtain ⟨probUnary, processUnary, stoppingUnary, boundUnary, stoppedValueUnary,
    filtrationUnary, integrabilityUnary, _sameRowsUnary, routeUnary, _provenanceUnary,
    _namecertUnary, endpointUnary, stoppedValueRow, integrabilityRow, _sameRowsSame, routeSame,
    _provenanceSame, endpointSame, _namecertSame, pkgSig⟩ := carrier
  have dependencyReadUnary : UnaryHistory dependencyRead :=
    unary_cont_closed endpointUnary routeUnary dependencyRoute
  exact And.intro probUnary
    (And.intro processUnary
      (And.intro stoppingUnary
        (And.intro boundUnary
          (And.intro stoppedValueUnary
            (And.intro filtrationUnary
              (And.intro integrabilityUnary
                (And.intro dependencyReadUnary
                  (And.intro stoppedValueRow
                    (And.intro integrabilityRow
                      (And.intro routeSame
                        (And.intro endpointSame pkgSig)))))))))))

theorem OptionalStoppingCarrier_post_stop_tail_erasure [AskSetup] [PackageSetup]
    {prob process stopping bound stoppedValue filtration integrability sameRows route provenance
      namecert endpoint process' stopping' filtration' integrability' sameRows' route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptionalStoppingCarrier prob process stopping bound stoppedValue filtration integrability sameRows
        route provenance namecert endpoint bundle pkg ->
      hsame process process' ->
        hsame stopping stopping' ->
          hsame filtration filtration' ->
            hsame integrability integrability' ->
              hsame sameRows sameRows' ->
                hsame route route' ->
                  Cont stopping' bound stoppedValue ->
                    Cont process' filtration' integrability' ->
                      hsame sameRows' (append prob process') ->
                        hsame route' (append stopping' bound) ->
                          OptionalStoppingCarrier prob process' stopping' bound stoppedValue
                              filtration' integrability' sameRows' route' provenance namecert endpoint
                              bundle pkg ∧
                            hsame stoppedValue stoppedValue := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameProcess sameStopping sameFiltration sameIntegrability sameRowsTransport
    routeTransport stoppedValueReadback integrabilityReadback sameRowsReadback routeReadback
  obtain ⟨probUnary, processUnary, stoppingUnary, boundUnary, stoppedValueUnary,
    filtrationUnary, integrabilityUnary, sameRowsUnary, routeUnary, provenanceUnary,
    namecertUnary, endpointUnary, _stoppedValueReadback, _integrabilityReadback,
    _sameRowsReadback, _routeReadback, provenanceSame, endpointSame, namecertSame,
    pkgSig⟩ := carrier
  have processUnary' : UnaryHistory process' :=
    unary_transport processUnary sameProcess
  have stoppingUnary' : UnaryHistory stopping' :=
    unary_transport stoppingUnary sameStopping
  have filtrationUnary' : UnaryHistory filtration' :=
    unary_transport filtrationUnary sameFiltration
  have integrabilityUnary' : UnaryHistory integrability' :=
    unary_transport integrabilityUnary sameIntegrability
  have sameRowsUnary' : UnaryHistory sameRows' :=
    unary_transport sameRowsUnary sameRowsTransport
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary routeTransport
  have endpointTailTransport :
      hsame (append stoppedValue integrability) (append stoppedValue integrability') := by
    cases sameIntegrability
    exact hsame_refl (append stoppedValue integrability)
  have provenanceSame' : hsame provenance (append stoppedValue integrability') :=
    hsame_trans provenanceSame endpointTailTransport
  have endpointSame' : hsame endpoint (append stoppedValue integrability') :=
    hsame_trans endpointSame endpointTailTransport
  exact
    ⟨⟨probUnary, processUnary', stoppingUnary', boundUnary, stoppedValueUnary,
      filtrationUnary', integrabilityUnary', sameRowsUnary', routeUnary', provenanceUnary,
      namecertUnary, endpointUnary, stoppedValueReadback, integrabilityReadback,
      sameRowsReadback, routeReadback, provenanceSame', endpointSame', namecertSame, pkgSig⟩,
      hsame_refl stoppedValue⟩

end BEDC.Derived.OptionalStoppingUp
