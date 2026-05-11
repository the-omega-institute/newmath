import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicPrecisionUp : Type where
  | mk :
      (precision radius window sameRows route provenance namecert ledger endpoint : BHist) →
        DyadicPrecisionUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def dyadicPrecisionToEventFlow : DyadicPrecisionUp → EventFlow
  | DyadicPrecisionUp.mk precision radius window sameRows route provenance namecert ledger
      endpoint =>
      [[BMark.b0], encodeBHist precision,
        [BMark.b1, BMark.b0], encodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b0], encodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist sameRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist namecert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          encodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
          encodeBHist endpoint]

private def dyadicPrecisionFromEventFlow : EventFlow → Option DyadicPrecisionUp
  | _tag0 :: precision :: _tag1 :: radius :: _tag2 :: window :: _tag3 :: sameRows ::
      _tag4 :: route :: _tag5 :: provenance :: _tag6 :: namecert :: _tag7 :: ledger ::
      _tag8 :: endpoint :: [] =>
      some
        (DyadicPrecisionUp.mk (decodeBHist precision) (decodeBHist radius)
          (decodeBHist window) (decodeBHist sameRows) (decodeBHist route)
          (decodeBHist provenance) (decodeBHist namecert) (decodeBHist ledger)
          (decodeBHist endpoint))
  | _ => none

private theorem dyadicPrecision_round_trip :
    ∀ x : DyadicPrecisionUp, dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) =
      some x := by
  intro x
  cases x with
  | mk precision radius window sameRows route provenance namecert ledger endpoint =>
      change
        some
          (DyadicPrecisionUp.mk (decodeBHist (encodeBHist precision))
            (decodeBHist (encodeBHist radius)) (decodeBHist (encodeBHist window))
            (decodeBHist (encodeBHist sameRows)) (decodeBHist (encodeBHist route))
            (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist namecert))
            (decodeBHist (encodeBHist ledger)) (decodeBHist (encodeBHist endpoint))) =
          some
            (DyadicPrecisionUp.mk precision radius window sameRows route provenance namecert
              ledger endpoint)
      simp only [decode_encode_bhist]

private theorem dyadicPrecisionToEventFlow_injective {x y : DyadicPrecisionUp} :
    dyadicPrecisionToEventFlow x = dyadicPrecisionToEventFlow y → x = y := by
  intro heq
  have hread :
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) =
        dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow y) :=
    congrArg dyadicPrecisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicPrecision_round_trip x).symm
      (Eq.trans hread (dyadicPrecision_round_trip y)))

instance dyadicPrecisionBHistCarrier : BHistCarrier DyadicPrecisionUp where
  toEventFlow := dyadicPrecisionToEventFlow
  fromEventFlow := dyadicPrecisionFromEventFlow

instance dyadicPrecisionChapterTasteGate : ChapterTasteGate DyadicPrecisionUp where
  round_trip := by
    intro x
    change dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x
    exact dyadicPrecision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicPrecisionToEventFlow_injective heq)

def DyadicPrecisionSchedulePacket [AskSetup] [PackageSetup]
    (precision radius window sameRows route provenance namecert ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory radius ∧ UnaryHistory window ∧
    UnaryHistory sameRows ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory namecert ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        Cont precision radius sameRows ∧ Cont sameRows window route ∧
          Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem DyadicPrecisionSchedule_realup_boundary [AskSetup] [PackageSetup]
    {precision radius window sameRows route provenance namecert ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicPrecisionSchedulePacket precision radius window sameRows route provenance namecert
        ledger endpoint bundle pkg ->
      UnaryHistory precision ∧ UnaryHistory radius ∧ UnaryHistory window ∧
        UnaryHistory sameRows ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
          UnaryHistory namecert ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            Cont precision radius sameRows ∧ Cont sameRows window route ∧
              Cont route provenance endpoint ∧ hsame sameRows (append precision radius) ∧
                hsame route (append sameRows window) ∧
                  hsame endpoint (append route provenance) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have radiusUnary : UnaryHistory radius :=
    packet.right.left
  have windowUnary : UnaryHistory window :=
    packet.right.right.left
  have sameRowsUnary : UnaryHistory sameRows :=
    packet.right.right.right.left
  have routeUnary : UnaryHistory route :=
    packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.left
  have namecertUnary : UnaryHistory namecert :=
    packet.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have sameRowsRoute : Cont precision radius sameRows :=
    packet.right.right.right.right.right.right.right.right.right.left
  have routeRow : Cont sameRows window route :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont route provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨precisionUnary,
      radiusUnary,
      windowUnary,
      sameRowsUnary,
      routeUnary,
      provenanceUnary,
      namecertUnary,
      ledgerUnary,
      endpointUnary,
      sameRowsRoute,
      routeRow,
      endpointRow,
      sameRowsRoute,
      routeRow,
      endpointRow,
      pkgSig⟩

def taste_gate : ChapterTasteGate DyadicPrecisionUp := dyadicPrecisionChapterTasteGate

end BEDC.Derived.DyadicPrecisionUp
