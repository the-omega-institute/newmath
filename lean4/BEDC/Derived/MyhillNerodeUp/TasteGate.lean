import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MyhillNerodeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MyhillNerodeUp : Type where
  | mk (Sigma W L E C D Q delta q0 F mu H R P N : BHist) : MyhillNerodeUp
  deriving DecidableEq

def myhillNerodeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: myhillNerodeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: myhillNerodeEncodeBHist h

def myhillNerodeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (myhillNerodeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (myhillNerodeDecodeBHist tail)

private theorem myhillNerodeDecodeEncodeBHist :
    ∀ h : BHist, myhillNerodeDecodeBHist (myhillNerodeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def myhillNerodeToEventFlow : MyhillNerodeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MyhillNerodeUp.mk Sigma W L E C D Q delta q0 F mu H R P N =>
      [myhillNerodeEncodeBHist Sigma,
        myhillNerodeEncodeBHist W,
        myhillNerodeEncodeBHist L,
        myhillNerodeEncodeBHist E,
        myhillNerodeEncodeBHist C,
        myhillNerodeEncodeBHist D,
        myhillNerodeEncodeBHist Q,
        myhillNerodeEncodeBHist delta,
        myhillNerodeEncodeBHist q0,
        myhillNerodeEncodeBHist F,
        myhillNerodeEncodeBHist mu,
        myhillNerodeEncodeBHist H,
        myhillNerodeEncodeBHist R,
        myhillNerodeEncodeBHist P,
        myhillNerodeEncodeBHist N]

private def myhillNerodeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => myhillNerodeEventAtDefault index rest

def myhillNerodeFromEventFlow (ef : EventFlow) : Option MyhillNerodeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MyhillNerodeUp.mk
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 0 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 1 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 2 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 3 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 4 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 5 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 6 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 7 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 8 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 9 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 10 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 11 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 12 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 13 ef))
      (myhillNerodeDecodeBHist (myhillNerodeEventAtDefault 14 ef)))

private theorem myhillNerodeRoundTrip :
    ∀ x : MyhillNerodeUp, myhillNerodeFromEventFlow (myhillNerodeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Sigma W L E C D Q delta q0 F mu H R P N =>
      change
        some
          (MyhillNerodeUp.mk
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist Sigma))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist W))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist L))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist E))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist C))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist D))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist Q))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist delta))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist q0))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist F))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist mu))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist H))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist R))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist P))
            (myhillNerodeDecodeBHist (myhillNerodeEncodeBHist N))) =
          some (MyhillNerodeUp.mk Sigma W L E C D Q delta q0 F mu H R P N)
      rw [myhillNerodeDecodeEncodeBHist Sigma,
        myhillNerodeDecodeEncodeBHist W,
        myhillNerodeDecodeEncodeBHist L,
        myhillNerodeDecodeEncodeBHist E,
        myhillNerodeDecodeEncodeBHist C,
        myhillNerodeDecodeEncodeBHist D,
        myhillNerodeDecodeEncodeBHist Q,
        myhillNerodeDecodeEncodeBHist delta,
        myhillNerodeDecodeEncodeBHist q0,
        myhillNerodeDecodeEncodeBHist F,
        myhillNerodeDecodeEncodeBHist mu,
        myhillNerodeDecodeEncodeBHist H,
        myhillNerodeDecodeEncodeBHist R,
        myhillNerodeDecodeEncodeBHist P,
        myhillNerodeDecodeEncodeBHist N]

private theorem myhillNerodeToEventFlow_injective {x y : MyhillNerodeUp} :
    myhillNerodeToEventFlow x = myhillNerodeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      myhillNerodeFromEventFlow (myhillNerodeToEventFlow x) =
        myhillNerodeFromEventFlow (myhillNerodeToEventFlow y) :=
    congrArg myhillNerodeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (myhillNerodeRoundTrip x).symm (Eq.trans hread (myhillNerodeRoundTrip y)))

private def myhillNerodeFields : MyhillNerodeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MyhillNerodeUp.mk Sigma W L E C D Q delta q0 F mu H R P N =>
      [Sigma, W, L, E, C, D, Q, delta, q0, F, mu, H, R, P, N]

private theorem myhillNerodeFieldFaithful :
    ∀ x y : MyhillNerodeUp, myhillNerodeFields x = myhillNerodeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Sigma1 W1 L1 E1 C1 D1 Q1 delta1 q01 F1 mu1 H1 R1 P1 N1 =>
      cases y with
      | mk Sigma2 W2 L2 E2 C2 D2 Q2 delta2 q02 F2 mu2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance myhillNerodeBHistCarrier : BHistCarrier MyhillNerodeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := myhillNerodeToEventFlow
  fromEventFlow := myhillNerodeFromEventFlow

instance myhillNerodeChapterTasteGate : ChapterTasteGate MyhillNerodeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change myhillNerodeFromEventFlow (myhillNerodeToEventFlow x) = some x
    exact myhillNerodeRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (myhillNerodeToEventFlow_injective heq)

instance myhillNerodeFieldFaithfulInstance : FieldFaithful MyhillNerodeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := myhillNerodeFields
  field_faithful := myhillNerodeFieldFaithful

instance myhillNerodeNontrivial : Nontrivial MyhillNerodeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MyhillNerodeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      MyhillNerodeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MyhillNerodeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  myhillNerodeChapterTasteGate

theorem MyhillNerodeTasteGate_single_carrier_alignment :
    (∀ h : BHist, myhillNerodeDecodeBHist (myhillNerodeEncodeBHist h) = h) ∧
      (∀ x : MyhillNerodeUp,
        myhillNerodeFromEventFlow (myhillNerodeToEventFlow x) = some x) ∧
        (∀ x y : MyhillNerodeUp,
          myhillNerodeToEventFlow x = myhillNerodeToEventFlow y → x = y) ∧
          myhillNerodeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨myhillNerodeDecodeEncodeBHist,
      myhillNerodeRoundTrip,
      (fun _ _ heq => myhillNerodeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MyhillNerodeUp
