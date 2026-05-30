import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithConvergenceUp : Type where
  | mk (D V U C B R L H K P N : BHist) : MooreSmithConvergenceUp
  deriving DecidableEq

def mooreSmithConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithConvergenceEncodeBHist h

def mooreSmithConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithConvergenceDecodeBHist tail)

private theorem MooreSmithConvergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mooreSmithConvergenceFields : MooreSmithConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithConvergenceUp.mk D V U C B R L H K P N => [D, V, U, C, B, R, L, H, K, P, N]

def mooreSmithConvergenceToEventFlow : MooreSmithConvergenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (mooreSmithConvergenceFields x).map mooreSmithConvergenceEncodeBHist

private def mooreSmithConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mooreSmithConvergenceEventAtDefault index rest

def mooreSmithConvergenceFromEventFlow (ef : EventFlow) : Option MooreSmithConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MooreSmithConvergenceUp.mk
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 0 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 1 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 2 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 3 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 4 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 5 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 6 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 7 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 8 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 9 ef))
      (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEventAtDefault 10 ef)))

private theorem MooreSmithConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MooreSmithConvergenceUp,
      mooreSmithConvergenceFromEventFlow (mooreSmithConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D V U C B R L H K P N =>
      change
        some
          (MooreSmithConvergenceUp.mk
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist D))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist V))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist U))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist C))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist B))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist R))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist L))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist H))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist K))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist P))
            (mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist N))) =
          some (MooreSmithConvergenceUp.mk D V U C B R L H K P N)
      rw [MooreSmithConvergenceTasteGate_single_carrier_alignment_decode D,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode V,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode U,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode C,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode B,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode R,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode L,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode H,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode K,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode P,
        MooreSmithConvergenceTasteGate_single_carrier_alignment_decode N]

private theorem MooreSmithConvergenceTasteGate_single_carrier_alignment_injective
    {x y : MooreSmithConvergenceUp} :
    mooreSmithConvergenceToEventFlow x = mooreSmithConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithConvergenceFromEventFlow (mooreSmithConvergenceToEventFlow x) =
        mooreSmithConvergenceFromEventFlow (mooreSmithConvergenceToEventFlow y) :=
    congrArg mooreSmithConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MooreSmithConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MooreSmithConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance mooreSmithConvergenceBHistCarrier : BHistCarrier MooreSmithConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithConvergenceToEventFlow
  fromEventFlow := mooreSmithConvergenceFromEventFlow

instance mooreSmithConvergenceChapterTasteGate :
    ChapterTasteGate MooreSmithConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mooreSmithConvergenceFromEventFlow (mooreSmithConvergenceToEventFlow x) = some x
    exact MooreSmithConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MooreSmithConvergenceTasteGate_single_carrier_alignment_injective heq)

theorem MooreSmithConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, mooreSmithConvergenceDecodeBHist (mooreSmithConvergenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MooreSmithConvergenceUp) ∧
        Nonempty (ChapterTasteGate MooreSmithConvergenceUp) ∧
          mooreSmithConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MooreSmithConvergenceTasteGate_single_carrier_alignment_decode,
      ⟨⟨mooreSmithConvergenceBHistCarrier⟩, ⟨mooreSmithConvergenceChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.MooreSmithConvergenceUp
