import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRealSequenceUp : Type where
  | mk (S W Q R I H C P N : BHist) : BoundedRealSequenceUp
  deriving DecidableEq

def BoundedRealSequenceTasteGate_single_carrier_alignment_encode :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BoundedRealSequenceTasteGate_single_carrier_alignment_encode h
  | BHist.e1 h => BMark.b1 :: BoundedRealSequenceTasteGate_single_carrier_alignment_encode h

def BoundedRealSequenceTasteGate_single_carrier_alignment_decode :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode tail)
  | BMark.b1 :: tail => BHist.e1
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode tail)

private theorem BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist,
      BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_encode h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BoundedRealSequenceTasteGate_single_carrier_alignment_fields :
    BoundedRealSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRealSequenceUp.mk S W Q R I H C P N => [S, W, Q, R, I, H, C, P, N]

def BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow :
    BoundedRealSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (BoundedRealSequenceTasteGate_single_carrier_alignment_fields x).map
        BoundedRealSequenceTasteGate_single_carrier_alignment_encode

private def BoundedRealSequenceTasteGate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BoundedRealSequenceTasteGate_single_carrier_alignment_event_at index rest

def BoundedRealSequenceTasteGate_single_carrier_alignment_from_event_flow
    (ef : EventFlow) : Option BoundedRealSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedRealSequenceUp.mk
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 0 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 1 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 2 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 3 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 4 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 5 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 6 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 7 ef))
      (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
        (BoundedRealSequenceTasteGate_single_carrier_alignment_event_at 8 ef)))

private theorem BoundedRealSequenceTasteGate_single_carrier_alignment_round_trip
    (x : BoundedRealSequenceUp) :
    BoundedRealSequenceTasteGate_single_carrier_alignment_from_event_flow
      (BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W Q R I H C P N =>
      change
        some
          (BoundedRealSequenceUp.mk
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode S))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode W))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode Q))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode R))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode I))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode H))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode C))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode P))
            (BoundedRealSequenceTasteGate_single_carrier_alignment_decode
              (BoundedRealSequenceTasteGate_single_carrier_alignment_encode N))) =
          some (BoundedRealSequenceUp.mk S W Q R I H C P N)
      rw [BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux S,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux W,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux Q,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux R,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux I,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux H,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux C,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux P,
        BoundedRealSequenceTasteGate_single_carrier_alignment_decode_aux N]

private theorem BoundedRealSequenceTasteGate_single_carrier_alignment_injective_aux
    {x y : BoundedRealSequenceUp} :
    BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow x =
      BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BoundedRealSequenceTasteGate_single_carrier_alignment_from_event_flow
          (BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow x) =
        BoundedRealSequenceTasteGate_single_carrier_alignment_from_event_flow
          (BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow y) :=
    congrArg BoundedRealSequenceTasteGate_single_carrier_alignment_from_event_flow heq
  exact Option.some.inj
    (Eq.trans (BoundedRealSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedRealSequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedRealSequenceTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : BoundedRealSequenceUp,
      BoundedRealSequenceTasteGate_single_carrier_alignment_fields x =
        BoundedRealSequenceTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ W₁ Q₁ R₁ I₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ W₂ Q₂ R₂ I₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance BoundedRealSequenceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow
  fromEventFlow := BoundedRealSequenceTasteGate_single_carrier_alignment_from_event_flow

instance BoundedRealSequenceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BoundedRealSequenceTasteGate_single_carrier_alignment_from_event_flow
        (BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow x) = some x
    exact BoundedRealSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedRealSequenceTasteGate_single_carrier_alignment_injective_aux heq)

instance BoundedRealSequenceTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BoundedRealSequenceTasteGate_single_carrier_alignment_fields
  field_faithful := BoundedRealSequenceTasteGate_single_carrier_alignment_fields_aux

instance BoundedRealSequenceTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial BoundedRealSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedRealSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedRealSequenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def BoundedRealSequenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BoundedRealSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BoundedRealSequenceTasteGate_single_carrier_alignment_ChapterTasteGate

theorem BoundedRealSequenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BoundedRealSequenceUp) ∧
      Nonempty (ChapterTasteGate BoundedRealSequenceUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨BoundedRealSequenceTasteGate_single_carrier_alignment_BHistCarrier⟩
  · exact ⟨BoundedRealSequenceTasteGate_single_carrier_alignment_ChapterTasteGate⟩

theorem BoundedRealSequenceFiniteWindow_bound
    {S W Q R I H C P N sealRead boundRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory I ->
            UnaryHistory H ->
              Cont S W Q ->
                Cont Q R sealRead ->
                  Cont sealRead I boundRead ->
                    Cont boundRead H C ->
                      UnaryHistory Q ∧ UnaryHistory sealRead ∧ UnaryHistory boundRead ∧
                        UnaryHistory C ∧
                          BHistCarrier.toEventFlow
                              (BoundedRealSequenceUp.mk S W Q R I H C P N) =
                            BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow
                              (BoundedRealSequenceUp.mk S W Q R I H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro sourceUnary windowUnary realUnary intervalUnary transportUnary sourceWindow
    sealRoute boundRoute consumerRoute
  have readbackUnary : UnaryHistory Q :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary realUnary sealRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed sealUnary intervalUnary boundRoute
  have consumerUnary : UnaryHistory C :=
    unary_cont_closed boundUnary transportUnary consumerRoute
  exact ⟨readbackUnary, sealUnary, boundUnary, consumerUnary, rfl⟩

theorem BoundedRealSequenceBolzanoWeierstrass_handoff
    {S W Q R I H C P N clusterRead boundRead handoffRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory I ->
            UnaryHistory H ->
              Cont S W Q ->
                Cont Q R clusterRead ->
                  Cont clusterRead I boundRead ->
                    Cont boundRead H handoffRead ->
                      UnaryHistory Q ∧ UnaryHistory clusterRead ∧ UnaryHistory boundRead ∧
                        UnaryHistory handoffRead ∧
                          BHistCarrier.toEventFlow
                              (BoundedRealSequenceUp.mk S W Q R I H C P N) =
                            BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow
                              (BoundedRealSequenceUp.mk S W Q R I H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro sourceUnary windowUnary realUnary intervalUnary transportUnary sourceWindow
    clusterRoute boundRoute handoffRoute
  have readbackUnary : UnaryHistory Q :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed readbackUnary realUnary clusterRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed clusterUnary intervalUnary boundRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed boundUnary transportUnary handoffRoute
  exact ⟨readbackUnary, clusterUnary, boundUnary, handoffUnary, rfl⟩

theorem BoundedRealSequenceWindow_envelope
    {S W Q R I H C P N sourceRead boundRead envelope : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory I ->
              UnaryHistory H ->
                Cont S W sourceRead ->
                  Cont sourceRead Q R ->
                    Cont R I boundRead ->
                      Cont boundRead H envelope ->
                        UnaryHistory sourceRead ∧ UnaryHistory boundRead ∧
                          UnaryHistory envelope ∧
                            BHistCarrier.toEventFlow
                                (BoundedRealSequenceUp.mk S W Q R I H C P N) =
                              BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow
                                (BoundedRealSequenceUp.mk S W Q R I H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro sourceUnary windowUnary readbackUnary _realUnary intervalUnary transportUnary
    sourceWindow sourceReadback realBound boundEnvelope
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have realRouteUnary : UnaryHistory R :=
    unary_cont_closed sourceReadUnary readbackUnary sourceReadback
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed realRouteUnary intervalUnary realBound
  have envelopeUnary : UnaryHistory envelope :=
    unary_cont_closed boundUnary transportUnary boundEnvelope
  exact ⟨sourceReadUnary, boundUnary, envelopeUnary, rfl⟩

theorem BoundedRealSequenceRegSeqRat_readback
    {S W Q R I H C P N windowRead sealRead boundRead attachedRead : BHist} :
    UnaryHistory W ->
      UnaryHistory Q ->
        UnaryHistory R ->
          UnaryHistory I ->
            UnaryHistory H ->
              Cont W Q windowRead ->
                Cont windowRead R sealRead ->
                  Cont sealRead I boundRead ->
                    Cont boundRead H attachedRead ->
                      UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory boundRead ∧ UnaryHistory attachedRead ∧
                          BHistCarrier.toEventFlow
                              (BoundedRealSequenceUp.mk S W Q R I H C P N) =
                            BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow
                              (BoundedRealSequenceUp.mk S W Q R I H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  intro windowUnary readbackUnary realUnary intervalUnary transportUnary windowRoute
    sealRoute boundRoute attachedRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary readbackUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary realUnary sealRoute
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed sealReadUnary intervalUnary boundRoute
  have attachedReadUnary : UnaryHistory attachedRead :=
    unary_cont_closed boundReadUnary transportUnary attachedRoute
  exact ⟨windowReadUnary, sealReadUnary, boundReadUnary, attachedReadUnary, rfl⟩

theorem BoundedRealSequenceBolzano_frontier
    {S W Q R I H C P N sourceRead readbackRead sealRead boundRead frontierRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory R ->
            UnaryHistory I ->
              UnaryHistory H ->
                Cont S W sourceRead ->
                  Cont sourceRead Q readbackRead ->
                    Cont readbackRead R sealRead ->
                      Cont sealRead I boundRead ->
                        Cont boundRead H frontierRead ->
                          UnaryHistory sourceRead ∧ UnaryHistory readbackRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory boundRead ∧
                              UnaryHistory frontierRead ∧
                                BHistCarrier.toEventFlow
                                    (BoundedRealSequenceUp.mk S W Q R I H C P N) =
                                  BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow
                                    (BoundedRealSequenceUp.mk S W Q R I H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory Cont
  intro sourceUnary windowUnary readbackUnary realUnary intervalUnary transportUnary
    sourceWindow readbackRoute sealRoute boundRoute frontierRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed sourceReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary realUnary sealRoute
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed sealReadUnary intervalUnary boundRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed boundReadUnary transportUnary frontierRoute
  exact
    ⟨sourceReadUnary, readbackReadUnary, sealReadUnary, boundReadUnary, frontierReadUnary,
      rfl⟩

end BEDC.Derived.BoundedRealSequenceUp
