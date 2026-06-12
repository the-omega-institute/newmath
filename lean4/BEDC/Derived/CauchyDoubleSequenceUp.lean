import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyDoubleSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyDoubleSequenceCarrier [AskSetup] [PackageSetup]
    (array schedule tolerance diagonal completion sealRow transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
    UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
      UnaryHistory provenance ∧ Cont array schedule diagonal ∧
        Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
          Cont array sealRow transport ∧ Cont transport localCert route ∧
            Cont route provenance sealRow ∧ PkgSig bundle provenance pkg

theorem CauchyDoubleSequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
                transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row sealRow ∧ UnaryHistory diagonal ∧ UnaryHistory completion)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
            Cont array schedule diagonal ∧ Cont schedule tolerance diagonal ∧
              Cont diagonal completion sealRow ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have diagonalUnary : UnaryHistory diagonal := carrier.right.right.right.left
  have completionUnary : UnaryHistory completion := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRow := carrier.right.right.right.right.right.left
  have arrayScheduleRoute : Cont array schedule diagonal :=
    carrier.right.right.right.right.right.right.right.left
  have scheduleToleranceRoute : Cont schedule tolerance diagonal :=
    carrier.right.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute : Cont diagonal completion sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have sourceAtSeal :
      hsame sealRow sealRow ∧
        CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
          transport route provenance localCert bundle pkg :=
    And.intro (hsame_refl sealRow) carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
                transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row sealRow ∧ UnaryHistory diagonal ∧ UnaryHistory completion)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceAtSeal
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
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact source.right
    }
    pattern_sound := by
      intro row source
      exact And.intro source.left (And.intro diagonalUnary completionUnary)
    ledger_sound := by
      intro row source
      exact And.intro source.left pkgSig
  }
  exact And.intro cert
    (And.intro arrayUnary
      (And.intro scheduleUnary
        (And.intro toleranceUnary
          (And.intro diagonalUnary
            (And.intro completionUnary
              (And.intro sealUnary
                (And.intro arrayScheduleRoute
                  (And.intro scheduleToleranceRoute
                    (And.intro diagonalCompletionRoute pkgSig)))))))))

theorem CauchyDoubleSequenceCarrier_diagonal_handoff [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow localCert consumer →
        UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
          UnaryHistory consumer ∧ Cont array schedule diagonal ∧
            Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
              PkgSig bundle provenance pkg := by
  intro carrier sealConsumer
  have diagonalUnary : UnaryHistory diagonal := carrier.right.right.right.left
  have completionUnary : UnaryHistory completion := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRow := carrier.right.right.right.right.right.left
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    unary_append_left_factor (routeProvenanceSeal ▸ sealUnary)
  have localCertUnary : UnaryHistory localCert :=
    unary_append_right_factor (transportLocalCertRoute ▸ routeUnary)
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary localCertUnary sealConsumer
  have arrayScheduleRoute : Cont array schedule diagonal :=
    carrier.right.right.right.right.right.right.right.left
  have scheduleToleranceRoute : Cont schedule tolerance diagonal :=
    carrier.right.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute : Cont diagonal completion sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact And.intro diagonalUnary
    (And.intro completionUnary
      (And.intro sealUnary
          (And.intro consumerUnary
            (And.intro arrayScheduleRoute
              (And.intro scheduleToleranceRoute
                (And.intro diagonalCompletionRoute pkgSig))))))

theorem CauchyDoubleSequenceCarrier_real_consumer_boundary [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow localCert consumer →
        UnaryHistory consumer ∧ Cont array schedule diagonal ∧
          Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
            Cont transport localCert route ∧ Cont route provenance sealRow ∧
              PkgSig bundle provenance pkg := by
  intro carrier sealConsumer
  have handoff :
      UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
        UnaryHistory consumer ∧ Cont array schedule diagonal ∧
          Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
            PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_diagonal_handoff carrier sealConsumer
  obtain ⟨_diagonalUnary, _completionUnary, _sealUnary, consumerUnary,
    arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute, pkgSig⟩ := handoff
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  exact
    ⟨consumerUnary, arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute,
      transportLocalCertRoute, routeProvenanceSeal, pkgSig⟩

theorem CauchyDoubleSequenceWindowDiagonalExhaustion [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert diagonalRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont array schedule diagonalRead →
        Cont diagonalRead tolerance boundedRead →
          PkgSig bundle boundedRead pkg →
            UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
              UnaryHistory diagonalRead ∧ UnaryHistory boundedRead ∧
                Cont array schedule diagonalRead ∧
                  Cont diagonalRead tolerance boundedRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundedRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig
  intro carrier arrayScheduleRead diagonalToleranceRead boundedPkg
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed arrayUnary scheduleUnary arrayScheduleRead
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed diagonalReadUnary toleranceUnary diagonalToleranceRead
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨arrayUnary, scheduleUnary, toleranceUnary, diagonalReadUnary, boundedReadUnary,
      arrayScheduleRead, diagonalToleranceRead, provenancePkg, boundedPkg⟩

theorem CauchyDoubleSequenceTwoAxisSealFactorization [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert diagonalRead sealRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont array schedule diagonalRead →
        Cont diagonalRead completion sealRead →
          Cont sealRead localCert consumer →
            PkgSig bundle consumer pkg →
              UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory completion ∧
                UnaryHistory diagonalRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory consumer ∧ Cont array schedule diagonalRead ∧
                    Cont diagonalRead completion sealRead ∧
                      Cont sealRead localCert consumer ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig
  intro carrier arrayScheduleRead diagonalCompletionRead sealConsumer consumerPkg
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have completionUnary : UnaryHistory completion := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRow := carrier.right.right.right.right.right.left
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed arrayUnary scheduleUnary arrayScheduleRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed diagonalReadUnary completionUnary diagonalCompletionRead
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    unary_append_left_factor (routeProvenanceSeal ▸ sealUnary)
  have localCertUnary : UnaryHistory localCert :=
    unary_append_right_factor (transportLocalCertRoute ▸ routeUnary)
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealReadUnary localCertUnary sealConsumer
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨arrayUnary, scheduleUnary, completionUnary, diagonalReadUnary, sealReadUnary,
      consumerUnary, arrayScheduleRead, diagonalCompletionRead, sealConsumer, provenancePkg,
      consumerPkg⟩

theorem CauchyDoubleSequenceCarrier_schedule_tail_exactness [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      diagonal' sealRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg ->
      hsame diagonal diagonal' ->
        Cont diagonal' completion sealRow' ->
          UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
            UnaryHistory diagonal ∧ UnaryHistory diagonal' ∧ UnaryHistory completion ∧
              UnaryHistory sealRow' ∧ Cont array schedule diagonal ∧
                Cont schedule tolerance diagonal ∧ Cont diagonal' completion sealRow' ∧
                  hsame sealRow sealRow' ∧ PkgSig bundle provenance pkg := by
  intro carrier sameDiagonal diagonalCompletionRoute'
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have diagonalUnary : UnaryHistory diagonal := carrier.right.right.right.left
  have completionUnary : UnaryHistory completion := carrier.right.right.right.right.left
  have arrayScheduleRoute : Cont array schedule diagonal :=
    carrier.right.right.right.right.right.right.right.left
  have scheduleToleranceRoute : Cont schedule tolerance diagonal :=
    carrier.right.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute : Cont diagonal completion sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have sealRowUnary' : UnaryHistory sealRow' :=
    unary_cont_closed diagonalUnary' completionUnary diagonalCompletionRoute'
  have sameSealRow : hsame sealRow sealRow' :=
    cont_respects_hsame sameDiagonal (hsame_refl completion) diagonalCompletionRoute
      diagonalCompletionRoute'
  exact
    ⟨arrayUnary, scheduleUnary, toleranceUnary, diagonalUnary, diagonalUnary',
      completionUnary, sealRowUnary', arrayScheduleRoute, scheduleToleranceRoute,
      diagonalCompletionRoute', sameSealRow, pkgSig⟩

theorem CauchyDoubleSequenceCarrier_completion_consumer_scope [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      consumer diagonal' sealRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      hsame diagonal diagonal' →
        Cont diagonal' completion sealRow' →
          Cont sealRow' localCert consumer →
            UnaryHistory consumer ∧ hsame sealRow sealRow' ∧
              Cont array schedule diagonal ∧ Cont schedule tolerance diagonal ∧
                Cont diagonal' completion sealRow' ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame
  intro carrier sameDiagonal diagonalCompletionRoute' sealConsumer
  have scheduleTail :
      UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
        UnaryHistory diagonal ∧ UnaryHistory diagonal' ∧ UnaryHistory completion ∧
          UnaryHistory sealRow' ∧ Cont array schedule diagonal ∧
            Cont schedule tolerance diagonal ∧ Cont diagonal' completion sealRow' ∧
              hsame sealRow sealRow' ∧ PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_schedule_tail_exactness carrier sameDiagonal
      diagonalCompletionRoute'
  obtain ⟨_arrayUnary, _scheduleUnary, _toleranceUnary, _diagonalUnary, _diagonalUnary',
    completionUnary, sealRowUnary', arrayScheduleRoute, scheduleToleranceRoute,
    diagonalCompletionRoute, sameSealRow, pkgSig⟩ := scheduleTail
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    unary_append_left_factor (routeProvenanceSeal ▸ carrier.right.right.right.right.right.left)
  have localCertUnary : UnaryHistory localCert :=
    unary_append_right_factor (transportLocalCertRoute ▸ routeUnary)
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealRowUnary' localCertUnary sealConsumer
  exact
    ⟨consumerUnary, sameSealRow, arrayScheduleRoute, scheduleToleranceRoute,
      diagonalCompletionRoute, pkgSig⟩

theorem CauchyDoubleSequenceCarrier_window_diagonal_exhaustion [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      arrayWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont array schedule arrayWindow →
        Cont arrayWindow tolerance diagonal →
          PkgSig bundle diagonal pkg →
            hsame diagonal (append (append array schedule) tolerance) ∧
              UnaryHistory diagonal ∧ UnaryHistory arrayWindow ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle diagonal pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory PkgSig
  intro carrier arrayWindowRoute diagonalRoute diagonalPkg
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have arrayWindowUnary : UnaryHistory arrayWindow :=
    unary_cont_closed arrayUnary scheduleUnary arrayWindowRoute
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed arrayWindowUnary toleranceUnary diagonalRoute
  have diagonalExact : hsame diagonal (append (append array schedule) tolerance) :=
    diagonalRoute.trans (congrArg (fun row => append row tolerance) arrayWindowRoute)
  exact ⟨diagonalExact, diagonalUnary, arrayWindowUnary, provenancePkg, diagonalPkg⟩

theorem CauchyDoubleSequenceCarrier_cofinal_tail_stability [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      schedule2 tolerance2 diagonal2 sealRow2 consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg ->
      hsame schedule schedule2 ->
        hsame tolerance tolerance2 ->
          Cont array schedule2 diagonal2 ->
            Cont schedule2 tolerance2 diagonal2 ->
              Cont diagonal2 completion sealRow2 ->
                Cont sealRow2 localCert consumer ->
                  UnaryHistory schedule2 ∧ UnaryHistory tolerance2 ∧
                    UnaryHistory diagonal2 ∧ UnaryHistory sealRow2 ∧
                      UnaryHistory consumer ∧ hsame sealRow sealRow2 ∧
                        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier sameSchedule sameTolerance arraySchedule2 scheduleTolerance2
    diagonalCompletion2 sealConsumer2
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have completionUnary : UnaryHistory completion := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRow := carrier.right.right.right.right.right.left
  have scheduleToleranceRoute : Cont schedule tolerance diagonal :=
    carrier.right.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute : Cont diagonal completion sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have schedule2Unary : UnaryHistory schedule2 :=
    unary_transport scheduleUnary sameSchedule
  have tolerance2Unary : UnaryHistory tolerance2 :=
    unary_transport toleranceUnary sameTolerance
  have diagonal2Unary : UnaryHistory diagonal2 :=
    unary_cont_closed arrayUnary schedule2Unary arraySchedule2
  have sameDiagonal : hsame diagonal diagonal2 :=
    cont_respects_hsame sameSchedule sameTolerance scheduleToleranceRoute scheduleTolerance2
  have sealRow2Unary : UnaryHistory sealRow2 :=
    unary_cont_closed diagonal2Unary completionUnary diagonalCompletion2
  have sameSealRow : hsame sealRow sealRow2 :=
    cont_respects_hsame sameDiagonal (hsame_refl completion) diagonalCompletionRoute
      diagonalCompletion2
  have routeUnary : UnaryHistory route :=
    unary_append_left_factor (routeProvenanceSeal ▸ sealUnary)
  have localCertUnary : UnaryHistory localCert :=
    unary_append_right_factor (transportLocalCertRoute ▸ routeUnary)
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealRow2Unary localCertUnary sealConsumer2
  exact
    ⟨schedule2Unary, tolerance2Unary, diagonal2Unary, sealRow2Unary, consumerUnary,
      sameSealRow, pkgSig⟩

theorem CauchyDoubleSequenceScopedDiagonalRoute [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow localCert consumer ->
        SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row array ∨ hsame row schedule ∨ hsame row tolerance ∨
                hsame row diagonal ∨ hsame row completion ∨ hsame row sealRow ∨
                  hsame row consumer)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont array schedule diagonal ∧
                Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
                  Cont sealRow localCert consumer ∧ PkgSig bundle provenance pkg)
            hsame ∧
          UnaryHistory consumer ∧ Cont array schedule diagonal ∧
            Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealConsumer
  have handoff :
      UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
        UnaryHistory consumer ∧ Cont array schedule diagonal ∧
          Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
            PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_diagonal_handoff carrier sealConsumer
  obtain ⟨_diagonalUnary, _completionUnary, _sealUnary, consumerUnary,
    arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute, pkgSig⟩ := handoff
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, arrayScheduleRoute, scheduleToleranceRoute,
            diagonalCompletionRoute, sealConsumer, pkgSig⟩
    }
  · exact
      ⟨consumerUnary, arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute,
        pkgSig⟩

theorem CauchyDoubleSequenceSealRouteDeterminacy [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      consumerLeft consumerRight : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow transport route
        provenance localCert bundle pkg →
      Cont sealRow localCert consumerLeft →
        Cont sealRow localCert consumerRight →
          hsame consumerLeft consumerRight ∧ UnaryHistory consumerLeft ∧
            UnaryHistory consumerRight ∧ Cont array schedule diagonal ∧
              Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier leftConsumer rightConsumer
  have sealUnary : UnaryHistory sealRow := carrier.right.right.right.right.right.left
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have routeUnary : UnaryHistory route :=
    unary_append_left_factor (routeProvenanceSeal ▸ sealUnary)
  have localCertUnary : UnaryHistory localCert :=
    unary_append_right_factor (transportLocalCertRoute ▸ routeUnary)
  have consumerLeftUnary : UnaryHistory consumerLeft :=
    unary_cont_closed sealUnary localCertUnary leftConsumer
  have consumerRightUnary : UnaryHistory consumerRight :=
    unary_cont_closed sealUnary localCertUnary rightConsumer
  have sameConsumers : hsame consumerLeft consumerRight :=
    cont_respects_hsame (hsame_refl sealRow) (hsame_refl localCert) leftConsumer
      rightConsumer
  have arrayScheduleRoute : Cont array schedule diagonal :=
    carrier.right.right.right.right.right.right.right.left
  have scheduleToleranceRoute : Cont schedule tolerance diagonal :=
    carrier.right.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute : Cont diagonal completion sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨sameConsumers, consumerLeftUnary, consumerRightUnary, arrayScheduleRoute,
      scheduleToleranceRoute, diagonalCompletionRoute, provenancePkg⟩

theorem CauchyDoubleSequenceDiagonalTailStability [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      array' schedule' tolerance' diagonal' completion' sealRow' transport' route' provenance'
      localCert' consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg ->
      CauchyDoubleSequenceCarrier array' schedule' tolerance' diagonal' completion' sealRow'
        transport' route' provenance' localCert' bundle pkg ->
        hsame array array' ->
          hsame schedule schedule' ->
            hsame tolerance tolerance' ->
              hsame completion completion' ->
                Cont sealRow' localCert' consumer ->
                  UnaryHistory diagonal' ∧ UnaryHistory sealRow' ∧ UnaryHistory consumer ∧
                    hsame diagonal diagonal' ∧ hsame sealRow sealRow' ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier carrier' sameArray sameSchedule _sameTolerance sameCompletion sealConsumer'
  have diagonalUnary' : UnaryHistory diagonal' := carrier'.right.right.right.left
  have sealUnary' : UnaryHistory sealRow' := carrier'.right.right.right.right.right.left
  have arrayScheduleRoute : Cont array schedule diagonal :=
    carrier.right.right.right.right.right.right.right.left
  have arrayScheduleRoute' : Cont array' schedule' diagonal' :=
    carrier'.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute : Cont diagonal completion sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute' : Cont diagonal' completion' sealRow' :=
    carrier'.right.right.right.right.right.right.right.right.right.left
  have transportLocalCertRoute' : Cont transport' localCert' route' :=
    carrier'.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal' : Cont route' provenance' sealRow' :=
    carrier'.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have pkgSig' : PkgSig bundle provenance' pkg :=
    carrier'.right.right.right.right.right.right.right.right.right.right.right.right.right
  have sameDiagonal : hsame diagonal diagonal' :=
    cont_respects_hsame sameArray sameSchedule arrayScheduleRoute arrayScheduleRoute'
  have sameSealRow : hsame sealRow sealRow' :=
    cont_respects_hsame sameDiagonal sameCompletion diagonalCompletionRoute
      diagonalCompletionRoute'
  have routeUnary' : UnaryHistory route' :=
    unary_append_left_factor (routeProvenanceSeal' ▸ sealUnary')
  have localCertUnary' : UnaryHistory localCert' :=
    unary_append_right_factor (transportLocalCertRoute' ▸ routeUnary')
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary' localCertUnary' sealConsumer'
  exact
    ⟨diagonalUnary', sealUnary', consumerUnary, sameDiagonal, sameSealRow, pkgSig, pkgSig'⟩

theorem CauchyDoubleSequenceScopedSurface [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow localCert consumer →
        SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row array ∨ hsame row schedule ∨ hsame row tolerance ∨
                hsame row diagonal ∨ hsame row completion ∨ hsame row sealRow ∨
                  hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                    hsame row localCert ∨ hsame row consumer)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont array schedule diagonal ∧
                Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
                  Cont transport localCert route ∧ Cont route provenance sealRow ∧
                    Cont sealRow localCert consumer ∧ PkgSig bundle provenance pkg)
            hsame := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealConsumer
  have handoff :
      UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
        UnaryHistory consumer ∧ Cont array schedule diagonal ∧
          Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
            PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_diagonal_handoff carrier sealConsumer
  obtain ⟨_diagonalUnary, _completionUnary, _sealUnary, consumerUnary,
    arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute,
    provenancePkg⟩ := handoff
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute,
          transportLocalCertRoute, routeProvenanceSeal, sealConsumer, provenancePkg⟩
  }

end BEDC.Derived.CauchyDoubleSequenceUp
