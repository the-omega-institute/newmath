import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChainConnectedMetricUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChainConnectedMetricUp : Type where
  | mk (X a b epsilon C D W Q E H R P N : BHist) : ChainConnectedMetricUp
  deriving DecidableEq

def chainConnectedMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: chainConnectedMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: chainConnectedMetricEncodeBHist h

def chainConnectedMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (chainConnectedMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (chainConnectedMetricDecodeBHist tail)

private theorem ChainConnectedMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def chainConnectedMetricToEventFlow : ChainConnectedMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChainConnectedMetricUp.mk X a b epsilon C D W Q E H R P N =>
      [[BMark.b0],
        chainConnectedMetricEncodeBHist X,
        [BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist a,
        [BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist b,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist epsilon,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        chainConnectedMetricEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        chainConnectedMetricEncodeBHist N]

private def chainConnectedMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => chainConnectedMetricEventAtDefault index rest

def chainConnectedMetricFromEventFlow (ef : EventFlow) : Option ChainConnectedMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ChainConnectedMetricUp.mk
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 1 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 3 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 5 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 7 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 9 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 11 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 13 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 15 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 17 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 19 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 21 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 23 ef))
      (chainConnectedMetricDecodeBHist (chainConnectedMetricEventAtDefault 25 ef)))

private theorem ChainConnectedMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChainConnectedMetricUp,
      chainConnectedMetricFromEventFlow (chainConnectedMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X a b epsilon C D W Q E H R P N =>
      change
        some
          (ChainConnectedMetricUp.mk
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist X))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist a))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist b))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist epsilon))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist C))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist D))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist W))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist Q))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist E))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist H))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist R))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist P))
            (chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist N))) =
          some (ChainConnectedMetricUp.mk X a b epsilon C D W Q E H R P N)
      rw [ChainConnectedMetricTasteGate_single_carrier_alignment_decode X,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode a,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode b,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode epsilon,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode C,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode D,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode W,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode Q,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode E,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode H,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode R,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode P,
        ChainConnectedMetricTasteGate_single_carrier_alignment_decode N]

private theorem ChainConnectedMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ChainConnectedMetricUp} :
    chainConnectedMetricToEventFlow x = chainConnectedMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      chainConnectedMetricFromEventFlow (chainConnectedMetricToEventFlow x) =
        chainConnectedMetricFromEventFlow (chainConnectedMetricToEventFlow y) :=
    congrArg chainConnectedMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ChainConnectedMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ChainConnectedMetricTasteGate_single_carrier_alignment_round_trip y)))

private def chainConnectedMetricFields : ChainConnectedMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChainConnectedMetricUp.mk X a b epsilon C D W Q E H R P N =>
      [X, a, b, epsilon, C, D, W, Q, E, H, R, P, N]

private theorem ChainConnectedMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : ChainConnectedMetricUp, chainConnectedMetricFields x = chainConnectedMetricFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 a1 b1 epsilon1 C1 D1 W1 Q1 E1 H1 R1 P1 N1 =>
      cases y with
      | mk X2 a2 b2 epsilon2 C2 D2 W2 Q2 E2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance chainConnectedMetricBHistCarrier : BHistCarrier ChainConnectedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := chainConnectedMetricToEventFlow
  fromEventFlow := chainConnectedMetricFromEventFlow

instance chainConnectedMetricChapterTasteGate : ChapterTasteGate ChainConnectedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change chainConnectedMetricFromEventFlow (chainConnectedMetricToEventFlow x) = some x
    exact ChainConnectedMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ChainConnectedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance chainConnectedMetricFieldFaithful : FieldFaithful ChainConnectedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := chainConnectedMetricFields
  field_faithful := ChainConnectedMetricTasteGate_single_carrier_alignment_fields

instance chainConnectedMetricNontrivial : Nontrivial ChainConnectedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChainConnectedMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ChainConnectedMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def chainConnectedMetricTasteGate : ChapterTasteGate ChainConnectedMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  chainConnectedMetricChapterTasteGate

theorem ChainConnectedMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, chainConnectedMetricDecodeBHist (chainConnectedMetricEncodeBHist h) = h) ∧
      (∀ x : ChainConnectedMetricUp,
        chainConnectedMetricFromEventFlow (chainConnectedMetricToEventFlow x) = some x) ∧
        (∀ x y : ChainConnectedMetricUp,
          chainConnectedMetricToEventFlow x = chainConnectedMetricToEventFlow y → x = y) ∧
          chainConnectedMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ChainConnectedMetricTasteGate_single_carrier_alignment_decode,
      ChainConnectedMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ChainConnectedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ChainConnectedMetricUp.TasteGate
