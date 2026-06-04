import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EpsilonDeltaLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EpsilonDeltaLimitUp : Type where
  | mk (X Y a L E D W R H C P N : BHist) : EpsilonDeltaLimitUp
  deriving DecidableEq

def epsilonDeltaLimitEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: epsilonDeltaLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: epsilonDeltaLimitEncodeBHist h

def epsilonDeltaLimitDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (epsilonDeltaLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (epsilonDeltaLimitDecodeBHist tail)

private theorem EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def epsilonDeltaLimitFields : EpsilonDeltaLimitUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EpsilonDeltaLimitUp.mk X Y a L E D W R H C P N =>
      [X, Y, a, L, E, D, W, R, H, C, P, N]

def epsilonDeltaLimitToEventFlow : EpsilonDeltaLimitUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (epsilonDeltaLimitFields x).map epsilonDeltaLimitEncodeBHist

private def epsilonDeltaLimitEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => epsilonDeltaLimitEventAtDefault index rest

def epsilonDeltaLimitFromEventFlow (ef : EventFlow) : Option EpsilonDeltaLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EpsilonDeltaLimitUp.mk
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 0 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 1 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 2 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 3 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 4 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 5 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 6 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 7 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 8 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 9 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 10 ef))
      (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEventAtDefault 11 ef)))

private theorem EpsilonDeltaLimitTasteGate_single_carrier_alignment_round_trip :
    forall x : EpsilonDeltaLimitUp,
      epsilonDeltaLimitFromEventFlow (epsilonDeltaLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y a L E D W R H C P N =>
      change
        some
          (EpsilonDeltaLimitUp.mk
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist X))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist Y))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist a))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist L))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist E))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist D))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist W))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist R))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist H))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist C))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist P))
            (epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist N))) =
          some (EpsilonDeltaLimitUp.mk X Y a L E D W R H C P N)
      rw [EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode X,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode Y,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode a,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode L,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode E,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode D,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode W,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode R,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode H,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode C,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode P,
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode N]

private theorem EpsilonDeltaLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EpsilonDeltaLimitUp} :
    epsilonDeltaLimitToEventFlow x = epsilonDeltaLimitToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      epsilonDeltaLimitFromEventFlow (epsilonDeltaLimitToEventFlow x) =
        epsilonDeltaLimitFromEventFlow (epsilonDeltaLimitToEventFlow y) :=
    congrArg epsilonDeltaLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EpsilonDeltaLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EpsilonDeltaLimitTasteGate_single_carrier_alignment_round_trip y)))

private theorem EpsilonDeltaLimitTasteGate_single_carrier_alignment_fields :
    forall x y : EpsilonDeltaLimitUp, epsilonDeltaLimitFields x = epsilonDeltaLimitFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 a1 L1 E1 D1 W1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 a2 L2 E2 D2 W2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance epsilonDeltaLimitBHistCarrier : BHistCarrier EpsilonDeltaLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := epsilonDeltaLimitToEventFlow
  fromEventFlow := epsilonDeltaLimitFromEventFlow

instance epsilonDeltaLimitChapterTasteGate : ChapterTasteGate EpsilonDeltaLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change epsilonDeltaLimitFromEventFlow (epsilonDeltaLimitToEventFlow x) = some x
    exact EpsilonDeltaLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EpsilonDeltaLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance epsilonDeltaLimitFieldFaithful : FieldFaithful EpsilonDeltaLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := epsilonDeltaLimitFields
  field_faithful := EpsilonDeltaLimitTasteGate_single_carrier_alignment_fields

theorem EpsilonDeltaLimitTasteGate_single_carrier_alignment :
    (forall h : BHist, epsilonDeltaLimitDecodeBHist (epsilonDeltaLimitEncodeBHist h) = h) ∧
      (forall x : EpsilonDeltaLimitUp,
        epsilonDeltaLimitFromEventFlow (epsilonDeltaLimitToEventFlow x) = some x) ∧
        (forall x y : EpsilonDeltaLimitUp,
          epsilonDeltaLimitToEventFlow x = epsilonDeltaLimitToEventFlow y -> x = y) ∧
          epsilonDeltaLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨EpsilonDeltaLimitTasteGate_single_carrier_alignment_decode,
      EpsilonDeltaLimitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        EpsilonDeltaLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EpsilonDeltaLimitUp
