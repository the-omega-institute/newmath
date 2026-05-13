import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

/-!
# ConsciousObserverStateUp TasteGate carrier.
-/

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def ConsciousObserverStateCarrier [AskSetup] [PackageSetup]
    (observer state recognition ledger gap transport route provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
    UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ UnaryHistory endpoint ∧
        Cont observer route endpoint ∧ Cont state route endpoint ∧
          Cont recognition ledger gap ∧ Cont transport provenance endpoint ∧
            PkgSig bundle endpoint pkg

theorem ConsciousObserverStateCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance name endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          Cont observer route row ∧ Cont state route row ∧ PkgSig bundle row pkg)
        (fun _row : BHist =>
          UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
            UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory endpoint)
        hsame := by
  intro carrier
  have observerUnary : UnaryHistory observer := carrier.left
  have stateUnary : UnaryHistory state := carrier.right.left
  have recognitionUnary : UnaryHistory recognition := carrier.right.right.left
  have ledgerUnary : UnaryHistory ledger := carrier.right.right.right.left
  have gapUnary : UnaryHistory gap := carrier.right.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.right.left
  have routeUnary : UnaryHistory route := carrier.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.right.left
  have nameUnary : UnaryHistory name := carrier.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have observerRoute : Cont observer route endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have stateRoute : Cont state route endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _left _right same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _left _right same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      have same : hsame row endpoint := source.right
      cases same
      exact And.intro observerRoute (And.intro stateRoute endpointPkg)
    ledger_sound := by
      intro _row _source
      exact
        And.intro observerUnary
          (And.intro stateUnary
            (And.intro recognitionUnary
              (And.intro ledgerUnary
                (And.intro gapUnary
                  (And.intro transportUnary
                    (And.intro routeUnary
                      (And.intro provenanceUnary
                        (And.intro nameUnary endpointUnary))))))))
  }

/-- Finite current-state observer packet with the nine displayed BEDC rows. -/
inductive ConsciousObserverStateUp : Type where
  | mk :
      (observerHistory currentState selfRecognition observationLedger gapAcknowledgement
        transport routes provenance nameCert : BHist) →
      ConsciousObserverStateUp
  deriving DecidableEq

def consciousObserverStateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: consciousObserverStateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: consciousObserverStateEncodeBHist h

def consciousObserverStateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (consciousObserverStateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (consciousObserverStateDecodeBHist tail)

private theorem ConsciousObserverStateTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      consciousObserverStateDecodeBHist (consciousObserverStateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def consciousObserverStateToEventFlow : ConsciousObserverStateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConsciousObserverStateUp.mk observerHistory currentState selfRecognition observationLedger
      gapAcknowledgement transport routes provenance nameCert =>
      [[BMark.b0],
        consciousObserverStateEncodeBHist observerHistory,
        [BMark.b1, BMark.b0],
        consciousObserverStateEncodeBHist currentState,
        [BMark.b1, BMark.b1, BMark.b0],
        consciousObserverStateEncodeBHist selfRecognition,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousObserverStateEncodeBHist observationLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousObserverStateEncodeBHist gapAcknowledgement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousObserverStateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousObserverStateEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        consciousObserverStateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        consciousObserverStateEncodeBHist nameCert]

def consciousObserverStateFromEventFlow : EventFlow → Option ConsciousObserverStateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observerHistory :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | currentState :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selfRecognition :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | observationLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gapAcknowledgement :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ConsciousObserverStateUp.mk
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    observerHistory)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    currentState)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    selfRecognition)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    observationLedger)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    gapAcknowledgement)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    transport)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    routes)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    provenance)
                                                                                  (consciousObserverStateDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ =>
                                                                              none

private theorem ConsciousObserverStateTasteGate_single_carrier_alignment_round :
    ∀ x : ConsciousObserverStateUp,
      consciousObserverStateFromEventFlow (consciousObserverStateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerHistory currentState selfRecognition observationLedger gapAcknowledgement
      transport routes provenance nameCert =>
      change
        some
          (ConsciousObserverStateUp.mk
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist observerHistory))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist currentState))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist selfRecognition))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist observationLedger))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist gapAcknowledgement))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist transport))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist routes))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist provenance))
            (consciousObserverStateDecodeBHist
              (consciousObserverStateEncodeBHist nameCert))) =
          some
            (ConsciousObserverStateUp.mk observerHistory currentState selfRecognition
              observationLedger gapAcknowledgement transport routes provenance nameCert)
      rw [ConsciousObserverStateTasteGate_single_carrier_alignment_decode observerHistory,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode currentState,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode selfRecognition,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode observationLedger,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode gapAcknowledgement,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode transport,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode routes,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode provenance,
        ConsciousObserverStateTasteGate_single_carrier_alignment_decode nameCert]

private theorem ConsciousObserverStateTasteGate_single_carrier_alignment_injective
    {x y : ConsciousObserverStateUp} :
    consciousObserverStateToEventFlow x = consciousObserverStateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      consciousObserverStateFromEventFlow (consciousObserverStateToEventFlow x) =
        consciousObserverStateFromEventFlow (consciousObserverStateToEventFlow y) :=
    congrArg consciousObserverStateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConsciousObserverStateTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread (ConsciousObserverStateTasteGate_single_carrier_alignment_round y)))

instance consciousObserverStateBHistCarrier : BHistCarrier ConsciousObserverStateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := consciousObserverStateToEventFlow
  fromEventFlow := consciousObserverStateFromEventFlow

instance consciousObserverStateChapterTasteGate : ChapterTasteGate ConsciousObserverStateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change consciousObserverStateFromEventFlow (consciousObserverStateToEventFlow x) = some x
    exact ConsciousObserverStateTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConsciousObserverStateTasteGate_single_carrier_alignment_injective heq)

theorem ConsciousObserverStateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      consciousObserverStateDecodeBHist (consciousObserverStateEncodeBHist h) = h) ∧
      (∀ x : ConsciousObserverStateUp,
        consciousObserverStateFromEventFlow (consciousObserverStateToEventFlow x) = some x) ∧
        (∀ x y : ConsciousObserverStateUp,
          consciousObserverStateToEventFlow x = consciousObserverStateToEventFlow y → x = y) ∧
          consciousObserverStateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ConsciousObserverStateTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ConsciousObserverStateTasteGate_single_carrier_alignment_round
    · constructor
      · intro x y heq
        exact ConsciousObserverStateTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ConsciousObserverStateUp
