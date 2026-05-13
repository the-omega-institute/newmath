import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History
import BEDC.Derived.RegularCauchyTailSelectorUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RegularCauchyTailSelectorUp

def CauchyLimitSealPacket [AskSetup] [PackageSetup]
    (source schedule ledger diagonal sealed transportRow provenance certificate : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory diagonal ∧
    UnaryHistory transportRow ∧ UnaryHistory provenance ∧ Cont schedule source ledger ∧
      Cont ledger diagonal sealed ∧ Cont sealed transportRow provenance ∧
        Cont provenance transportRow certificate ∧ PkgSig bundle certificate pkg

theorem CauchyLimitSealPacket_window_factorization [AskSetup] [PackageSetup]
    {source schedule ledger diagonal sealed transportRow provenance certificate window observation
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealPacket source schedule ledger diagonal sealed transportRow provenance certificate
        bundle pkg ->
      Cont schedule source window ->
        Cont window ledger observation ->
          Cont observation diagonal realRead ->
            hsame ledger observation ->
              UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                Cont schedule source window ∧ Cont window ledger observation ∧
                  Cont observation diagonal realRead ∧ hsame sealed realRead ∧
                    PkgSig bundle certificate pkg := by
  intro packet scheduleSourceWindow windowLedgerObservation observationDiagonalRead
    sameLedgerObservation
  obtain ⟨sourceUnary, scheduleUnary, diagonalUnary, _transportUnary, _provenanceUnary,
    _scheduleSourceLedger, ledgerDiagonalSealed, _sealedTransportProvenance,
    _provenanceTransportCertificate, certificatePkg⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary sourceUnary _scheduleSourceLedger
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have sealedSameRead : hsame sealed realRead :=
    cont_respects_hsame sameLedgerObservation (hsame_refl diagonal) ledgerDiagonalSealed
      observationDiagonalRead
  exact
    ⟨windowUnary, observationUnary, realReadUnary, scheduleSourceWindow,
      windowLedgerObservation, observationDiagonalRead, sealedSameRead, certificatePkg⟩

def CauchyLimitSealCarrier [AskSetup] [PackageSetup]
    (source schedule dyadic diagonal «seal» transport provenance localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory dyadic ∧
    UnaryHistory diagonal ∧ UnaryHistory «seal» ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ UnaryHistory localCert ∧ UnaryHistory endpoint ∧
        Cont source schedule dyadic ∧ Cont dyadic diagonal «seal» ∧
          Cont «seal» transport provenance ∧ Cont provenance localCert endpoint ∧
            hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg

theorem CauchyLimitSealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal «seal» transport provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
        localCert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyLimitSealCarrier source schedule dyadic diagonal «seal» transport provenance
            localCert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem CauchyLimitSealCarrier_dyadic_handoff [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint window
      observation realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg ->
      Cont source schedule window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            hsame dyadic observation ->
              UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                Cont source schedule window ∧ Cont window dyadic observation ∧
                  Cont observation diagonal realRead ∧ hsame sealRow realRead ∧
                    PkgSig bundle endpoint pkg := by
  intro carrier sourceScheduleWindow windowDyadicObservation observationDiagonalRead
    sameDyadicObservation
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have sealSameRead : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalRead
  exact
    ⟨windowUnary, observationUnary, realReadUnary, sourceScheduleWindow,
      windowDyadicObservation, observationDiagonalRead, sealSameRead, endpointPkg⟩

theorem CauchyLimitSealCarrier_realup_consumer_boundary [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont endpoint sealRow realRead ->
        UnaryHistory realRead ∧ Cont endpoint sealRow realRead ∧
          hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg := by
  intro carrier endpointSealRead
  rcases carrier with
    ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, sealUnary,
      _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
      _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
      _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩
  exact
    ⟨unary_cont_closed endpointUnary sealUnary endpointSealRead, endpointSealRead,
      sameEndpoint, endpointPkg⟩

theorem CauchyLimitSealCarrier_verification_handoff [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            hsame dyadic observation ->
              UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                hsame sealRow realRead ∧ hsame endpoint (append provenance localCert) ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    sameDyadicObservation
  rcases carrier with
    ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
      _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
      _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
      _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have sameSealRead : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalRead
  exact
    ⟨windowUnary, observationUnary, realReadUnary, sameSealRead, sameEndpoint,
      endpointPkg⟩

theorem CauchyLimitSealCarrier_scheduled_window_pullback [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            Cont realRead endpoint consumerRead ->
              hsame dyadic observation ->
                UnaryHistory window /\ UnaryHistory observation /\ UnaryHistory realRead /\
                  UnaryHistory consumerRead /\ hsame sealRow realRead /\
                    hsame endpoint (append provenance localCert) /\
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    readEndpointConsumer sameDyadicObservation
  have handoff :=
    CauchyLimitSealCarrier_verification_handoff carrier scheduleSourceWindow
      windowDyadicObservation observationDiagonalRead sameDyadicObservation
  obtain ⟨windowUnary, observationUnary, realReadUnary, sameSealRead, sameEndpoint,
    endpointPkg⟩ := handoff
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpointCarrier, _endpointPkgCarrier⟩ := carrier
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed realReadUnary endpointUnary readEndpointConsumer
  exact
    ⟨windowUnary, observationUnary, realReadUnary, consumerReadUnary, sameSealRead,
      sameEndpoint, endpointPkg⟩

theorem CauchyLimitSealCarrier_tail_budget_meet [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      precision stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead :
        BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                hsame dyadic budgetRead ->
                  hsame selectorDyadic dyadic ->
                    UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory selectorRead ∧
                        hsame sealRow completionRead ∧ hsame selectorDyadic budgetRead ∧
                          PkgSig sealBundle endpoint sealPkg ∧
                            PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_precisionUnary, _streamUnary, regularityUnary, _selectorDyadicUnary,
    _selectorSealUnary, witnessUnary, _selectorTransportUnary, _routesUnary,
    _selectorProvenanceUnary, _selectorNameUnary, _streamRegularityWitness,
    _witnessSelectorDyadicSeal, _sealTransportRoutes, _routesProvenanceName,
    selectorPkgSig⟩ := selectorPacket
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceBudget
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary dyadicUnary budgetDyadicRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetReadUnary diagonalUnary readDiagonalCompletion
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed witnessUnary regularityUnary witnessRegularityRead
  have sameSealCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicBudget (hsame_refl diagonal) dyadicDiagonalSeal
      readDiagonalCompletion
  have sameSelectorBudget : hsame selectorDyadic budgetRead :=
    hsame_trans sameSelectorDyadic sameDyadicBudget
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
      sameSealCompletion, sameSelectorBudget, endpointPkg, selectorPkgSig⟩

theorem CauchyLimitSealCarrier_selector_budget_transport [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead
      transportedBudgetRead transportedCompletionRead transportedSelectorRead : BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                hsame dyadic budgetRead ->
                  hsame selectorDyadic dyadic ->
                    hsame budgetRead transportedBudgetRead ->
                      hsame completionRead transportedCompletionRead ->
                        hsame selectorRead transportedSelectorRead ->
                          UnaryHistory transportedBudgetRead /\
                            UnaryHistory transportedCompletionRead /\
                              UnaryHistory transportedSelectorRead /\
                                hsame sealRow transportedCompletionRead /\
                                  hsame selectorDyadic transportedBudgetRead /\
                                    PkgSig sealBundle endpoint sealPkg /\
                                      PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic sameBudgetTransport
    sameCompletionTransport sameSelectorTransport
  have meet :=
    CauchyLimitSealCarrier_tail_budget_meet carrier selectorPacket scheduleSourceBudget
      budgetDyadicRead readDiagonalCompletion witnessRegularityRead sameDyadicBudget
      sameSelectorDyadic
  obtain ⟨_budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
    sameSealCompletion, sameSelectorBudget, endpointPkg, selectorPkgSig⟩ := meet
  have transportedBudgetUnary : UnaryHistory transportedBudgetRead :=
    unary_transport budgetReadUnary sameBudgetTransport
  have transportedCompletionUnary : UnaryHistory transportedCompletionRead :=
    unary_transport completionReadUnary sameCompletionTransport
  have transportedSelectorUnary : UnaryHistory transportedSelectorRead :=
    unary_transport selectorReadUnary sameSelectorTransport
  have sameSealTransportedCompletion : hsame sealRow transportedCompletionRead :=
    hsame_trans sameSealCompletion sameCompletionTransport
  have sameSelectorTransportedBudget : hsame selectorDyadic transportedBudgetRead :=
    hsame_trans sameSelectorBudget sameBudgetTransport
  exact
    ⟨transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
      sameSealTransportedCompletion, sameSelectorTransportedBudget, endpointPkg,
      selectorPkgSig⟩

theorem CauchyLimitSealCarrier_budget_selector_coherence [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead
      transportedBudgetRead transportedCompletionRead transportedSelectorRead rootRead : BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                hsame dyadic budgetRead ->
                  hsame selectorDyadic dyadic ->
                    hsame budgetRead transportedBudgetRead ->
                      hsame completionRead transportedCompletionRead ->
                        hsame selectorRead transportedSelectorRead ->
                          Cont transportedCompletionRead endpoint rootRead ->
                            UnaryHistory transportedBudgetRead /\
                              UnaryHistory transportedCompletionRead /\
                                UnaryHistory transportedSelectorRead /\ UnaryHistory rootRead /\
                                  hsame sealRow transportedCompletionRead /\
                                    hsame selectorDyadic transportedBudgetRead /\
                                      PkgSig sealBundle endpoint sealPkg /\
                                        PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic sameBudgetTransport
    sameCompletionTransport sameSelectorTransport completionEndpointRoot
  have transported :=
    CauchyLimitSealCarrier_selector_budget_transport carrier selectorPacket scheduleSourceBudget
      budgetDyadicRead readDiagonalCompletion witnessRegularityRead sameDyadicBudget
      sameSelectorDyadic sameBudgetTransport sameCompletionTransport sameSelectorTransport
  obtain ⟨transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
    sameSealTransportedCompletion, sameSelectorTransportedBudget, endpointPkg,
    selectorPkgSig⟩ := transported
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, _endpointPkgCarrier⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed transportedCompletionUnary endpointUnary completionEndpointRoot
  exact
    ⟨transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
      rootReadUnary, sameSealTransportedCompletion, sameSelectorTransportedBudget,
      endpointPkg, selectorPkgSig⟩

theorem CauchyLimitSealCarrier_choice_free_selector_admission [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint
      precision stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead :
        BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                hsame dyadic budgetRead ->
                  hsame selectorDyadic dyadic ->
                    UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory selectorRead ∧
                        hsame sealRow completionRead ∧ hsame selectorDyadic budgetRead ∧
                          hsame endpoint (append provenance localCert) ∧
                            PkgSig sealBundle endpoint sealPkg ∧
                              PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic
  have meet :=
    CauchyLimitSealCarrier_tail_budget_meet carrier selectorPacket scheduleSourceBudget
      budgetDyadicRead readDiagonalCompletion witnessRegularityRead sameDyadicBudget
      sameSelectorDyadic
  obtain ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
    sameSealCompletion, sameSelectorBudget, endpointPkg, selectorPkgSig⟩ := meet
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, _endpointPkg⟩ := carrier
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
      sameSealCompletion, sameSelectorBudget, sameEndpoint, endpointPkg, selectorPkgSig⟩

theorem CauchyLimitSealCarrier_choice_free_selector_stability [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead
      transportedBudgetRead transportedCompletionRead transportedSelectorRead : BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                hsame dyadic budgetRead ->
                  hsame selectorDyadic dyadic ->
                    hsame budgetRead transportedBudgetRead ->
                      hsame completionRead transportedCompletionRead ->
                        hsame selectorRead transportedSelectorRead ->
                          UnaryHistory transportedBudgetRead ∧
                            UnaryHistory transportedCompletionRead ∧
                              UnaryHistory transportedSelectorRead ∧
                                hsame sealRow transportedCompletionRead ∧
                                  hsame selectorDyadic transportedBudgetRead ∧
                                    hsame endpoint (append provenance localCert) ∧
                                      PkgSig sealBundle endpoint sealPkg ∧
                                        PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead sameDyadicBudget sameSelectorDyadic sameBudgetTransport
    sameCompletionTransport sameSelectorTransport
  have transported :=
    CauchyLimitSealCarrier_selector_budget_transport carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      sameDyadicBudget sameSelectorDyadic sameBudgetTransport sameCompletionTransport
      sameSelectorTransport
  obtain ⟨transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
    sameSealTransportedCompletion, sameSelectorTransportedBudget, endpointPkg,
    selectorPkgSig⟩ := transported
  obtain ⟨_sourceUnary, _scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, _endpointPkg⟩ := carrier
  exact
    ⟨transportedBudgetUnary, transportedCompletionUnary, transportedSelectorUnary,
      sameSealTransportedCompletion, sameSelectorTransportedBudget, sameEndpoint,
      endpointPkg, selectorPkgSig⟩

theorem CauchyLimitSealCarrier_root_budget_seal_coverage [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead rootRead :
        BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                Cont completionRead endpoint rootRead ->
                  hsame dyadic budgetRead ->
                    hsame selectorDyadic dyadic ->
                      UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                        UnaryHistory completionRead ∧ UnaryHistory selectorRead ∧
                          UnaryHistory rootRead ∧ hsame sealRow completionRead ∧
                            hsame selectorDyadic budgetRead ∧
                              PkgSig sealBundle endpoint sealPkg ∧
                                PkgSig selectorBundle selectorName selectorPkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_precisionUnary, _streamUnary, regularityUnary, _selectorDyadicUnary,
    _selectorSealUnary, witnessUnary, _selectorTransportUnary, _routesUnary,
    _selectorProvenanceUnary, _selectorNameUnary, _streamRegularityWitness,
    _witnessSelectorDyadicSeal, _sealTransportRoutes, _routesProvenanceName,
    selectorPkgSig⟩ := selectorPacket
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceBudget
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary dyadicUnary budgetDyadicRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetReadUnary diagonalUnary readDiagonalCompletion
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed witnessUnary regularityUnary witnessRegularityRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed completionReadUnary endpointUnary completionEndpointRoot
  have sameSealCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicBudget (hsame_refl diagonal) dyadicDiagonalSeal
      readDiagonalCompletion
  have sameSelectorBudget : hsame selectorDyadic budgetRead :=
    hsame_trans sameSelectorDyadic sameDyadicBudget
  exact
    ⟨budgetWindowUnary, budgetReadUnary, completionReadUnary, selectorReadUnary,
      rootReadUnary, sameSealCompletion, sameSelectorBudget, endpointPkg, selectorPkgSig⟩

theorem CauchyLimitSealCarrier_tail_budget_consumer_normal_form [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint precision
      stream regularity selectorDyadic selectorSeal witness selectorTransport routes
      selectorProvenance selectorName budgetWindow budgetRead completionRead selectorRead rootRead
      hostTail : BHist}
    {sealBundle selectorBundle : ProbeBundle ProbeName} {sealPkg selectorPkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint sealBundle sealPkg ->
      RegularCauchyTailSelectorPacket precision stream regularity selectorDyadic selectorSeal
          witness selectorTransport routes selectorProvenance selectorName selectorBundle
          selectorPkg ->
        Cont schedule source budgetWindow ->
          Cont budgetWindow dyadic budgetRead ->
            Cont budgetRead diagonal completionRead ->
              Cont witness regularity selectorRead ->
                Cont completionRead endpoint rootRead ->
                  hsame dyadic budgetRead ->
                    hsame selectorDyadic dyadic ->
                      UnaryHistory rootRead /\
                        Cont schedule (append source (append dyadic (append diagonal endpoint)))
                          rootRead /\
                          hsame sealRow completionRead /\ hsame selectorDyadic budgetRead /\
                            PkgSig sealBundle endpoint sealPkg /\
                              PkgSig selectorBundle selectorName selectorPkg /\
                                (Cont rootRead (BHist.e0 hostTail) schedule -> False) /\
                                  (Cont rootRead (BHist.e1 hostTail) schedule -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectorPacket scheduleSourceBudget budgetDyadicRead readDiagonalCompletion
    witnessRegularityRead completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  have coverage :=
    CauchyLimitSealCarrier_root_budget_seal_coverage carrier selectorPacket
      scheduleSourceBudget budgetDyadicRead readDiagonalCompletion witnessRegularityRead
      completionEndpointRoot sameDyadicBudget sameSelectorDyadic
  obtain ⟨_budgetWindowUnary, _budgetReadUnary, _completionReadUnary, _selectorReadUnary,
    rootReadUnary, sameSealCompletion, sameSelectorBudget, endpointPkg, selectorPkgSig⟩ :=
      coverage
  have scheduleToRoot :
      Cont schedule (append source (append dyadic (append diagonal endpoint))) rootRead := by
    cases scheduleSourceBudget
    cases budgetDyadicRead
    cases readDiagonalCompletion
    cases completionEndpointRoot
    exact
      (append_assoc (append (append schedule source) dyadic) diagonal endpoint).trans
        ((append_assoc (append schedule source) dyadic (append diagonal endpoint)).trans
          (append_assoc schedule source (append dyadic (append diagonal endpoint))))
  exact
    ⟨rootReadUnary, scheduleToRoot, sameSealCompletion, sameSelectorBudget, endpointPkg,
      selectorPkgSig,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left scheduleToRoot hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right scheduleToRoot hostReturn)⟩

end BEDC.Derived.CauchyLimitSealUp
