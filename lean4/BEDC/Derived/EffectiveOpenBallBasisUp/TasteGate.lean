import BEDC.Derived.EffectiveOpenBallBasisUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveOpenBallBasisUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def effectiveOpenBallBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveOpenBallBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveOpenBallBasisEncodeBHist h

def effectiveOpenBallBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveOpenBallBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveOpenBallBasisDecodeBHist tail)

private theorem EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveOpenBallBasisFields : EffectiveOpenBallBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveOpenBallBasisUp.mk M C D W R E T H K P N => [M, C, D, W, R, E, T, H, K, P, N]

def effectiveOpenBallBasisToEventFlow : EffectiveOpenBallBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (effectiveOpenBallBasisFields x).map effectiveOpenBallBasisEncodeBHist

private def effectiveOpenBallBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveOpenBallBasisEventAtDefault index rest

def effectiveOpenBallBasisFromEventFlow (ef : EventFlow) : Option EffectiveOpenBallBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectiveOpenBallBasisUp.mk
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 0 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 1 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 2 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 3 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 4 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 5 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 6 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 7 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 8 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 9 ef))
      (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEventAtDefault 10 ef)))

private theorem EffectiveOpenBallBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EffectiveOpenBallBasisUp,
      effectiveOpenBallBasisFromEventFlow (effectiveOpenBallBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M C D W R E T H K P N =>
      change
        some
          (EffectiveOpenBallBasisUp.mk
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist M))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist C))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist D))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist W))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist R))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist E))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist T))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist H))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist K))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist P))
            (effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist N))) =
          some (EffectiveOpenBallBasisUp.mk M C D W R E T H K P N)
      rw [EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode M,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode C,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode D,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode W,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode R,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode E,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode T,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode H,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode K,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode P,
        EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode N]

private theorem effectiveOpenBallBasisToEventFlow_injective
    {x y : EffectiveOpenBallBasisUp} :
    effectiveOpenBallBasisToEventFlow x = effectiveOpenBallBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveOpenBallBasisFromEventFlow (effectiveOpenBallBasisToEventFlow x) =
        effectiveOpenBallBasisFromEventFlow (effectiveOpenBallBasisToEventFlow y) :=
    congrArg effectiveOpenBallBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EffectiveOpenBallBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EffectiveOpenBallBasisTasteGate_single_carrier_alignment_round_trip y)))

instance effectiveOpenBallBasisBHistCarrier : BHistCarrier EffectiveOpenBallBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveOpenBallBasisToEventFlow
  fromEventFlow := effectiveOpenBallBasisFromEventFlow

instance effectiveOpenBallBasisChapterTasteGate :
    ChapterTasteGate EffectiveOpenBallBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveOpenBallBasisFromEventFlow (effectiveOpenBallBasisToEventFlow x) = some x
    exact EffectiveOpenBallBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveOpenBallBasisToEventFlow_injective heq)

def taste_gate : ChapterTasteGate EffectiveOpenBallBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveOpenBallBasisChapterTasteGate

theorem EffectiveOpenBallBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      effectiveOpenBallBasisDecodeBHist (effectiveOpenBallBasisEncodeBHist h) = h) ∧
      (∀ x : EffectiveOpenBallBasisUp,
        effectiveOpenBallBasisFromEventFlow (effectiveOpenBallBasisToEventFlow x) = some x) ∧
      (∀ x y : EffectiveOpenBallBasisUp,
        effectiveOpenBallBasisToEventFlow x = effectiveOpenBallBasisToEventFlow y → x = y) ∧
      effectiveOpenBallBasisFields (EffectiveOpenBallBasisUp.mk M C D W R E T H K P N) =
        [M, C, D, W, R, E, T, H, K, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨EffectiveOpenBallBasisTasteGate_single_carrier_alignment_decode,
      EffectiveOpenBallBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => effectiveOpenBallBasisToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EffectiveOpenBallBasisUp
