import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Unary.Closure
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicPrecisionUp : Type where
  | mk :
      (precision radius window transport provenance cert ledger endpoint : BHist) ->
        DyadicPrecisionUp
  deriving DecidableEq

def DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist : BHist -> RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist h
  | BHist.e1 h => BMark.b1 :: DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist h

def DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist : RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist tail)
  | BMark.b1 :: tail => BHist.e1 (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist tail)

private theorem DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist :
    forall h : BHist, DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow : DyadicPrecisionUp -> EventFlow
  | DyadicPrecisionUp.mk precision radius window transport provenance cert ledger endpoint =>
      [DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist precision, DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist radius, DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window, DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport,
        DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance, DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert, DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger, DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint]

def DyadicPrecisionSchedulePacket_namecert_obligations_from_event_flow : EventFlow -> Option DyadicPrecisionUp
  | [precision, radius, window, transport, provenance, cert, ledger, endpoint] =>
      some (DyadicPrecisionUp.mk (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist precision) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist radius)
        (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist window) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist transport) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist provenance)
        (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist cert) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist ledger) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist endpoint))
  | _ => none

private theorem DyadicPrecisionSchedulePacket_namecert_obligations_round_trip :
    forall x : DyadicPrecisionUp, DyadicPrecisionSchedulePacket_namecert_obligations_from_event_flow (DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow x) =
      some x := by
  intro x
  cases x with
  | mk precision radius window transport provenance cert ledger endpoint =>
      change
        some (DyadicPrecisionUp.mk (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist precision))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist radius)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
            some (DyadicPrecisionUp.mk precision radius window transport provenance cert ledger
              endpoint)
      have hPrecision :
          some (DyadicPrecisionUp.mk (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist precision))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist radius)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist radius))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk row (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist radius))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist precision)
      have hRadius :
          some (DyadicPrecisionUp.mk precision (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist radius))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision radius (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision row (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist radius)
      have hWindow :
          some (DyadicPrecisionUp.mk precision radius (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist window))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision radius window
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius row
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist window)
      have hTransport :
          some (DyadicPrecisionUp.mk precision radius window
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist transport)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision radius window transport
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window row
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist transport)
      have hProvenance :
          some (DyadicPrecisionUp.mk precision radius window transport
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist provenance)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision radius window transport provenance
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window transport row
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist provenance)
      have hCert :
          some (DyadicPrecisionUp.mk precision radius window transport provenance
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist cert)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger))
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision radius window transport provenance cert
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window transport provenance row
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist cert)
      have hLedger :
          some (DyadicPrecisionUp.mk precision radius window transport provenance cert
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist ledger)) (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision radius window transport provenance cert ledger
                (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window transport provenance cert row
              (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist ledger)
      have hEndpoint :
          some (DyadicPrecisionUp.mk precision radius window transport provenance cert ledger
            (DyadicPrecisionSchedulePacket_namecert_obligations_decode_bhist (DyadicPrecisionSchedulePacket_namecert_obligations_encode_bhist endpoint))) =
              some (DyadicPrecisionUp.mk precision radius window transport provenance cert ledger
                endpoint) :=
        congrArg
          (fun row =>
            some (DyadicPrecisionUp.mk precision radius window transport provenance cert ledger
              row))
          (DyadicPrecisionSchedulePacket_namecert_obligations_decode_encode_bhist endpoint)
      exact Eq.trans hPrecision (Eq.trans hRadius (Eq.trans hWindow
        (Eq.trans hTransport
          (Eq.trans hProvenance (Eq.trans hCert (Eq.trans hLedger hEndpoint))))))

private theorem DyadicPrecisionSchedulePacket_namecert_obligations_eventflow_injective
    {x y : DyadicPrecisionUp} :
    DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow x = DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow y -> x = y := by
  intro heq
  have hread :
      DyadicPrecisionSchedulePacket_namecert_obligations_from_event_flow (DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow x) =
        DyadicPrecisionSchedulePacket_namecert_obligations_from_event_flow (DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow y) :=
    congrArg DyadicPrecisionSchedulePacket_namecert_obligations_from_event_flow heq
  exact Option.some.inj
    (Eq.trans (DyadicPrecisionSchedulePacket_namecert_obligations_round_trip x).symm
      (Eq.trans hread (DyadicPrecisionSchedulePacket_namecert_obligations_round_trip y)))

instance dyadicPrecisionBHistCarrier : BHistCarrier DyadicPrecisionUp where
  toEventFlow := DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow
  fromEventFlow := DyadicPrecisionSchedulePacket_namecert_obligations_from_event_flow

instance dyadicPrecisionChapterTasteGate : ChapterTasteGate DyadicPrecisionUp where
  round_trip := by
    intro x
    change DyadicPrecisionSchedulePacket_namecert_obligations_from_event_flow (DyadicPrecisionSchedulePacket_namecert_obligations_to_event_flow x) = some x
    exact DyadicPrecisionSchedulePacket_namecert_obligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicPrecisionSchedulePacket_namecert_obligations_eventflow_injective heq)

def DyadicPrecisionSchedulePacket [AskSetup] [PackageSetup]
    (precision radius window transport provenance cert ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory radius ∧ UnaryHistory window ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
      UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont precision radius transport ∧
        Cont window transport provenance ∧ Cont provenance cert ledger ∧
          Cont ledger cert endpoint ∧ PkgSig bundle endpoint pkg

theorem DyadicPrecisionSchedulePacket_namecert_obligations [AskSetup] [PackageSetup]
    {precision radius window transport provenance cert ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicPrecisionSchedulePacket precision radius window transport provenance cert ledger
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicPrecisionSchedulePacket precision radius window transport provenance cert ledger
            endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          DyadicPrecisionSchedulePacket precision radius window transport provenance cert ledger
            endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          DyadicPrecisionSchedulePacket precision radius window transport provenance cert ledger
            endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  constructor
  · constructor
    · exact Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row row' same source
      exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
  · intro row source
    exact source
  · intro row source
    exact source

end BEDC.Derived.DyadicPrecisionUp
