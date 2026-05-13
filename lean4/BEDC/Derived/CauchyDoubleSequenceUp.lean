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

end BEDC.Derived.CauchyDoubleSequenceUp
