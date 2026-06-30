import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BetaSubstitutionDischargeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BetaSubstitutionDischargeUp : Type where
  | mk (G d b a c s h r p n : BHist) : BetaSubstitutionDischargeUp
  deriving DecidableEq

def betaSubstitutionDischargeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: betaSubstitutionDischargeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: betaSubstitutionDischargeEncodeBHist h

def betaSubstitutionDischargeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (betaSubstitutionDischargeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (betaSubstitutionDischargeDecodeBHist tail)

private theorem betaSubstitutionDischargeDecodeEncode :
    ∀ h : BHist,
      betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def betaSubstitutionDischargeToEventFlow : BetaSubstitutionDischargeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BetaSubstitutionDischargeUp.mk G d b a c s h r p n =>
      [betaSubstitutionDischargeEncodeBHist G,
        betaSubstitutionDischargeEncodeBHist d,
        betaSubstitutionDischargeEncodeBHist b,
        betaSubstitutionDischargeEncodeBHist a,
        betaSubstitutionDischargeEncodeBHist c,
        betaSubstitutionDischargeEncodeBHist s,
        betaSubstitutionDischargeEncodeBHist h,
        betaSubstitutionDischargeEncodeBHist r,
        betaSubstitutionDischargeEncodeBHist p,
        betaSubstitutionDischargeEncodeBHist n]

private def betaSubstitutionDischargeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => betaSubstitutionDischargeEventAt index rest

def betaSubstitutionDischargeFromEventFlow (ef : EventFlow) : Option BetaSubstitutionDischargeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BetaSubstitutionDischargeUp.mk
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 0 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 1 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 2 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 3 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 4 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 5 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 6 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 7 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 8 ef))
      (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEventAt 9 ef)))

private theorem betaSubstitutionDischargeRoundTrip (x : BetaSubstitutionDischargeUp) :
    betaSubstitutionDischargeFromEventFlow (betaSubstitutionDischargeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G d b a c s h r p n =>
      change
        some
          (BetaSubstitutionDischargeUp.mk
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist G))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist d))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist b))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist a))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist c))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist s))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist h))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist r))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist p))
            (betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist n))) =
          some (BetaSubstitutionDischargeUp.mk G d b a c s h r p n)
      rw [betaSubstitutionDischargeDecodeEncode G, betaSubstitutionDischargeDecodeEncode d,
        betaSubstitutionDischargeDecodeEncode b, betaSubstitutionDischargeDecodeEncode a,
        betaSubstitutionDischargeDecodeEncode c, betaSubstitutionDischargeDecodeEncode s,
        betaSubstitutionDischargeDecodeEncode h, betaSubstitutionDischargeDecodeEncode r,
        betaSubstitutionDischargeDecodeEncode p, betaSubstitutionDischargeDecodeEncode n]

private theorem betaSubstitutionDischargeToEventFlow_injective
    {x y : BetaSubstitutionDischargeUp} :
    betaSubstitutionDischargeToEventFlow x = betaSubstitutionDischargeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      betaSubstitutionDischargeFromEventFlow (betaSubstitutionDischargeToEventFlow x) =
        betaSubstitutionDischargeFromEventFlow (betaSubstitutionDischargeToEventFlow y) :=
    congrArg betaSubstitutionDischargeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (betaSubstitutionDischargeRoundTrip x).symm
      (Eq.trans hread (betaSubstitutionDischargeRoundTrip y)))

instance betaSubstitutionDischargeBHistCarrier : BHistCarrier BetaSubstitutionDischargeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := betaSubstitutionDischargeToEventFlow
  fromEventFlow := betaSubstitutionDischargeFromEventFlow

instance betaSubstitutionDischargeChapterTasteGate :
    ChapterTasteGate BetaSubstitutionDischargeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change betaSubstitutionDischargeFromEventFlow
      (betaSubstitutionDischargeToEventFlow x) = some x
    exact betaSubstitutionDischargeRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (betaSubstitutionDischargeToEventFlow_injective heq)

theorem BetaSubstitutionDischargeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      betaSubstitutionDischargeDecodeBHist (betaSubstitutionDischargeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BetaSubstitutionDischargeUp) ∧
        Nonempty (ChapterTasteGate BetaSubstitutionDischargeUp) ∧
          betaSubstitutionDischargeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨betaSubstitutionDischargeDecodeEncode,
      ⟨betaSubstitutionDischargeBHistCarrier⟩,
      ⟨betaSubstitutionDischargeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BetaSubstitutionDischargeUp
