import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyLimitClassifierLockUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyLimitClassifierLockUp : Type where
  | mk (X μ L U S W Q D E H C P N : BHist) : CauchyLimitClassifierLockUp
  deriving DecidableEq

def cauchyLimitClassifierLockEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyLimitClassifierLockEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyLimitClassifierLockEncodeBHist h

def cauchyLimitClassifierLockDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyLimitClassifierLockDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyLimitClassifierLockDecodeBHist tail)

private theorem cauchyLimitClassifierLock_decode_encode_bhist :
    ∀ h : BHist, cauchyLimitClassifierLockDecodeBHist
      (cauchyLimitClassifierLockEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyLimitClassifierLockFields : CauchyLimitClassifierLockUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyLimitClassifierLockUp.mk X μ L U S W Q D E H C P N =>
      [X, μ, L, U, S, W, Q, D, E, H, C, P, N]

def cauchyLimitClassifierLockToEventFlow : CauchyLimitClassifierLockUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyLimitClassifierLockFields x).map cauchyLimitClassifierLockEncodeBHist

private def cauchyLimitClassifierLockEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyLimitClassifierLockEventAt index rest

def cauchyLimitClassifierLockFromEventFlow
    (ef : EventFlow) : Option CauchyLimitClassifierLockUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyLimitClassifierLockUp.mk
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 0 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 1 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 2 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 3 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 4 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 5 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 6 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 7 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 8 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 9 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 10 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 11 ef))
      (cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEventAt 12 ef)))

private theorem cauchyLimitClassifierLock_round_trip (x : CauchyLimitClassifierLockUp) :
    cauchyLimitClassifierLockFromEventFlow (cauchyLimitClassifierLockToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X μ L U S W Q D E H C P N =>
      change
        some
          (CauchyLimitClassifierLockUp.mk
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist X))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist μ))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist L))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist U))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist S))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist W))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist Q))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist D))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist E))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist H))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist C))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist P))
            (cauchyLimitClassifierLockDecodeBHist
              (cauchyLimitClassifierLockEncodeBHist N))) =
          some (CauchyLimitClassifierLockUp.mk X μ L U S W Q D E H C P N)
      rw [cauchyLimitClassifierLock_decode_encode_bhist X,
        cauchyLimitClassifierLock_decode_encode_bhist μ,
        cauchyLimitClassifierLock_decode_encode_bhist L,
        cauchyLimitClassifierLock_decode_encode_bhist U,
        cauchyLimitClassifierLock_decode_encode_bhist S,
        cauchyLimitClassifierLock_decode_encode_bhist W,
        cauchyLimitClassifierLock_decode_encode_bhist Q,
        cauchyLimitClassifierLock_decode_encode_bhist D,
        cauchyLimitClassifierLock_decode_encode_bhist E,
        cauchyLimitClassifierLock_decode_encode_bhist H,
        cauchyLimitClassifierLock_decode_encode_bhist C,
        cauchyLimitClassifierLock_decode_encode_bhist P,
        cauchyLimitClassifierLock_decode_encode_bhist N]

private theorem cauchyLimitClassifierLockToEventFlow_injective
    {x y : CauchyLimitClassifierLockUp} :
    cauchyLimitClassifierLockToEventFlow x = cauchyLimitClassifierLockToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyLimitClassifierLockFromEventFlow
          (cauchyLimitClassifierLockToEventFlow x) =
        cauchyLimitClassifierLockFromEventFlow
          (cauchyLimitClassifierLockToEventFlow y) :=
    congrArg cauchyLimitClassifierLockFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyLimitClassifierLock_round_trip x).symm
      (Eq.trans hread (cauchyLimitClassifierLock_round_trip y)))

instance cauchyLimitClassifierLockBHistCarrier :
    BHistCarrier CauchyLimitClassifierLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyLimitClassifierLockToEventFlow
  fromEventFlow := cauchyLimitClassifierLockFromEventFlow

instance cauchyLimitClassifierLockChapterTasteGate :
    ChapterTasteGate CauchyLimitClassifierLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyLimitClassifierLockFromEventFlow
        (cauchyLimitClassifierLockToEventFlow x) = some x
    exact cauchyLimitClassifierLock_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyLimitClassifierLockToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyLimitClassifierLockUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyLimitClassifierLockChapterTasteGate

theorem CauchyLimitClassifierLockTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyLimitClassifierLockDecodeBHist (cauchyLimitClassifierLockEncodeBHist h) = h) ∧
      (∀ x : CauchyLimitClassifierLockUp,
        cauchyLimitClassifierLockFromEventFlow (cauchyLimitClassifierLockToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyLimitClassifierLockUp,
          cauchyLimitClassifierLockToEventFlow x = cauchyLimitClassifierLockToEventFlow y →
            x = y) ∧
          cauchyLimitClassifierLockEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyLimitClassifierLock_decode_encode_bhist,
      cauchyLimitClassifierLock_round_trip,
      (fun _ _ heq => cauchyLimitClassifierLockToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyLimitClassifierLockUp
