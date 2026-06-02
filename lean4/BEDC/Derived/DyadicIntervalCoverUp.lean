import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalCoverUp : Type where
  | mk (L U M R V W Q A H C P N : BHist) : DyadicIntervalCoverUp
  deriving DecidableEq

def dyadicIntervalCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalCoverEncodeBHist h

def dyadicIntervalCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalCoverDecodeBHist tail)

private theorem DyadicIntervalCoverRealWindowHandoffObligation_decode :
    ∀ h : BHist, dyadicIntervalCoverDecodeBHist
      (dyadicIntervalCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalCoverFields : DyadicIntervalCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalCoverUp.mk L U M R V W Q A H C P N => [L, U, M, R, V, W, Q, A, H, C, P, N]

def dyadicIntervalCoverToEventFlow : DyadicIntervalCoverUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicIntervalCoverFields x).map dyadicIntervalCoverEncodeBHist

private def dyadicIntervalCoverEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalCoverEventAtDefault index rest

def dyadicIntervalCoverFromEventFlow
    (ef : EventFlow) : Option DyadicIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalCoverUp.mk
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 0 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 1 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 2 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 3 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 4 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 5 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 6 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 7 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 8 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 9 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 10 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAtDefault 11 ef)))

private theorem DyadicIntervalCoverRealWindowHandoffObligation_round_trip :
    ∀ x : DyadicIntervalCoverUp,
      dyadicIntervalCoverFromEventFlow
        (dyadicIntervalCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk L U M R V W Q A H C P N =>
      change
        some
          (DyadicIntervalCoverUp.mk
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist L))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist U))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist M))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist R))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist V))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist W))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist Q))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist A))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist H))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist C))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist P))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist N))) =
          some (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N)
      rw [DyadicIntervalCoverRealWindowHandoffObligation_decode L,
        DyadicIntervalCoverRealWindowHandoffObligation_decode U,
        DyadicIntervalCoverRealWindowHandoffObligation_decode M,
        DyadicIntervalCoverRealWindowHandoffObligation_decode R,
        DyadicIntervalCoverRealWindowHandoffObligation_decode V,
        DyadicIntervalCoverRealWindowHandoffObligation_decode W,
        DyadicIntervalCoverRealWindowHandoffObligation_decode Q,
        DyadicIntervalCoverRealWindowHandoffObligation_decode A,
        DyadicIntervalCoverRealWindowHandoffObligation_decode H,
        DyadicIntervalCoverRealWindowHandoffObligation_decode C,
        DyadicIntervalCoverRealWindowHandoffObligation_decode P,
        DyadicIntervalCoverRealWindowHandoffObligation_decode N]

private theorem DyadicIntervalCoverRealWindowHandoffObligation_toEventFlow_injective
    {x y : DyadicIntervalCoverUp} :
    dyadicIntervalCoverToEventFlow x = dyadicIntervalCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) =
        dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow y) :=
    congrArg dyadicIntervalCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicIntervalCoverRealWindowHandoffObligation_round_trip x).symm
      (Eq.trans hread
        (DyadicIntervalCoverRealWindowHandoffObligation_round_trip y)))

private theorem DyadicIntervalCoverRealWindowHandoffObligation_fields :
    ∀ x y : DyadicIntervalCoverUp,
      dyadicIntervalCoverFields x = dyadicIntervalCoverFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 M1 R1 V1 W1 Q1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 M2 R2 V2 W2 Q2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicIntervalCoverBHistCarrier : BHistCarrier DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalCoverToEventFlow
  fromEventFlow := dyadicIntervalCoverFromEventFlow

instance dyadicIntervalCoverChapterTasteGate :
    ChapterTasteGate DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x
    exact DyadicIntervalCoverRealWindowHandoffObligation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalCoverRealWindowHandoffObligation_toEventFlow_injective heq)

instance dyadicIntervalCoverFieldFaithful :
    FieldFaithful DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalCoverFields
  field_faithful := DyadicIntervalCoverRealWindowHandoffObligation_fields

instance dyadicIntervalCoverNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicIntervalCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicIntervalCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalCoverChapterTasteGate

theorem DyadicIntervalCoverRealWindowHandoffObligation (x : DyadicIntervalCoverUp) :
    ∃ L U M R V W Q A H C P N : BHist,
      x = DyadicIntervalCoverUp.mk L U M R V W Q A H C P N ∧
        dyadicIntervalCoverFields x = [L, U, M, R, V, W, Q, A, H, C, P, N] ∧
          dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x ∧
            dyadicIntervalCoverEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              dyadicIntervalCoverEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U M R V W Q A H C P N =>
      exact
        ⟨L, U, M, R, V, W, Q, A, H, C, P, N, rfl, rfl,
          DyadicIntervalCoverRealWindowHandoffObligation_round_trip
            (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N),
          rfl, rfl⟩

theorem DyadicIntervalCoverWindowMembershipTransport (x : DyadicIntervalCoverUp) :
    ∃ L U M R V W Q A H C P N : BHist,
      x = DyadicIntervalCoverUp.mk L U M R V W Q A H C P N ∧
        dyadicIntervalCoverFields x = [L, U, M, R, V, W, Q, A, H, C, P, N] ∧
          dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x ∧
            dyadicIntervalCoverEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U M R V W Q A H C P N =>
      exact
        ⟨L, U, M, R, V, W, Q, A, H, C, P, N, rfl, rfl,
          DyadicIntervalCoverRealWindowHandoffObligation_round_trip
            (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N),
          rfl⟩

end BEDC.Derived.DyadicIntervalCoverUp
