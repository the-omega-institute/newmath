import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCutCarrier [AskSetup] [PackageSetup]
    (lower upper window handoff sealRow transportRow route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont lower upper window ∧
    Cont window handoff transportRow ∧
      Cont transportRow route provenance ∧
        Cont provenance localCert sealRow ∧
          PkgSig bundle provenance pkg ∧ hsame sealRow handoff ∧ hsame sealRow provenance

theorem LocatedCutCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row handoff)
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.left)
    ledger_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.right)
  }

theorem LocatedCutCarrier_seal_boundary_exactness [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      hsame handoff provenance ∧ Cont window handoff transportRow ∧
        Cont provenance localCert sealRow ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_windowRoute, handoffRoute, _provenanceRoute, sealRoute, packageSig, sameSealHandoff,
    sameSealProvenance⟩ := carrier
  have sameHandoffProvenance : hsame handoff provenance :=
    hsame_trans (hsame_symm sameSealHandoff) sameSealProvenance
  exact ⟨sameHandoffProvenance, handoffRoute, sealRoute, packageSig⟩

theorem LocatedCutCarrier_classifier_transport [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert lower' upper'
      window' handoff' sealRow' transportRow' route' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance
        localCert bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          hsame handoff handoff' ->
            hsame route route' ->
              hsame localCert localCert' ->
                Cont lower' upper' window' ->
                  Cont window' handoff' transportRow' ->
                    Cont transportRow' route' provenance' ->
                      Cont provenance' localCert' sealRow' ->
                        PkgSig bundle provenance' pkg ->
                          LocatedCutCarrier lower' upper' window' handoff' sealRow'
                              transportRow' route' provenance' localCert' bundle pkg ∧
                            hsame window window' ∧ hsame transportRow transportRow' ∧
                              hsame provenance provenance' ∧ hsame sealRow sealRow' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameLower sameUpper sameHandoff sameRoute sameLocalCert lowerUpperWindow'
    windowHandoffTransport' transportRouteProvenance' provenanceLocalCertSeal'
    provenancePkg'
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    provenanceLocalCertSeal, _provenancePkg, sameSealHandoff, sameSealProvenance⟩ :=
    carrier
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameLower sameUpper lowerUpperWindow lowerUpperWindow'
  have sameTransportRow : hsame transportRow transportRow' :=
    cont_respects_hsame sameWindow sameHandoff windowHandoffTransport windowHandoffTransport'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransportRow sameRoute transportRouteProvenance
      transportRouteProvenance'
  have sameSealRow : hsame sealRow sealRow' :=
    cont_respects_hsame sameProvenance sameLocalCert provenanceLocalCertSeal
      provenanceLocalCertSeal'
  have sameSealHandoff' : hsame sealRow' handoff' :=
    hsame_trans (hsame_symm sameSealRow) (hsame_trans sameSealHandoff sameHandoff)
  have sameSealProvenance' : hsame sealRow' provenance' :=
    hsame_trans (hsame_symm sameSealRow) (hsame_trans sameSealProvenance sameProvenance)
  have transported :
      LocatedCutCarrier lower' upper' window' handoff' sealRow' transportRow' route'
          provenance' localCert' bundle pkg :=
    ⟨lowerUpperWindow', windowHandoffTransport', transportRouteProvenance',
      provenanceLocalCertSeal', provenancePkg', sameSealHandoff', sameSealProvenance'⟩
  exact ⟨transported, sameWindow, sameTransportRow, sameProvenance, sameSealRow⟩

theorem LocatedCutCarrier_located_window_exactness [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                UnaryHistory window ∧ UnaryHistory transportRow ∧ UnaryHistory provenance ∧
                  UnaryHistory sealRow ∧ Cont lower upper window ∧
                    Cont window handoff transportRow ∧
                      Cont transportRow route provenance ∧
                        Cont provenance localCert sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    provenanceLocalCertSeal, provenancePkg, _sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed lowerUnary upperUnary lowerUpperWindow
  have transportUnary : UnaryHistory transportRow :=
    unary_cont_closed windowUnary handoffUnary windowHandoffTransport
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary routeUnary transportRouteProvenance
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalCertSeal
  exact ⟨windowUnary, transportUnary, provenanceUnary, sealUnary, lowerUpperWindow,
    windowHandoffTransport, transportRouteProvenance, provenanceLocalCertSeal, provenancePkg⟩

theorem LocatedCutCarrier_window_handoff_totality [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff route consumer ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory consumer ∧ Cont lower upper window ∧
                      Cont window handoff transportRow ∧ Cont transportRow route provenance ∧
                        Cont handoff route consumer ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle consumer pkg ∧ hsame sealRow handoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier _lowerUnary _upperUnary handoffUnary routeUnary _localCertUnary handoffRouteConsumer
    consumerPkg
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary routeUnary handoffRouteConsumer
  exact ⟨consumerUnary, lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    handoffRouteConsumer, provenancePkg, consumerPkg, sameSealHandoff⟩

end BEDC.Derived.LocatedCutUp
