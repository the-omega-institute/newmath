import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EgorovUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EgorovUp : Type where
  | mk (M Omega F X S R A W U L H C P N : BHist) : EgorovUp
  deriving DecidableEq

def egorovEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: egorovEncodeBHist h
  | BHist.e1 h => BMark.b1 :: egorovEncodeBHist h

def egorovDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (egorovDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (egorovDecodeBHist tail)

private theorem EgorovTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, egorovDecodeBHist (egorovEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def egorovFields : EgorovUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EgorovUp.mk M Omega F X S R A W U L H C P N =>
      [M, Omega, F, X, S, R, A, W, U, L, H, C, P, N]

def egorovToEventFlow : EgorovUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (egorovFields x).map egorovEncodeBHist

private def egorovEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => egorovEventAt index rest

def egorovFromEventFlow (ef : EventFlow) : Option EgorovUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EgorovUp.mk
      (egorovDecodeBHist (egorovEventAt 0 ef))
      (egorovDecodeBHist (egorovEventAt 1 ef))
      (egorovDecodeBHist (egorovEventAt 2 ef))
      (egorovDecodeBHist (egorovEventAt 3 ef))
      (egorovDecodeBHist (egorovEventAt 4 ef))
      (egorovDecodeBHist (egorovEventAt 5 ef))
      (egorovDecodeBHist (egorovEventAt 6 ef))
      (egorovDecodeBHist (egorovEventAt 7 ef))
      (egorovDecodeBHist (egorovEventAt 8 ef))
      (egorovDecodeBHist (egorovEventAt 9 ef))
      (egorovDecodeBHist (egorovEventAt 10 ef))
      (egorovDecodeBHist (egorovEventAt 11 ef))
      (egorovDecodeBHist (egorovEventAt 12 ef))
      (egorovDecodeBHist (egorovEventAt 13 ef)))

private theorem EgorovTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EgorovUp, egorovFromEventFlow (egorovToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M Omega F X S R A W U L H C P N =>
      change
        some
          (EgorovUp.mk
            (egorovDecodeBHist (egorovEncodeBHist M))
            (egorovDecodeBHist (egorovEncodeBHist Omega))
            (egorovDecodeBHist (egorovEncodeBHist F))
            (egorovDecodeBHist (egorovEncodeBHist X))
            (egorovDecodeBHist (egorovEncodeBHist S))
            (egorovDecodeBHist (egorovEncodeBHist R))
            (egorovDecodeBHist (egorovEncodeBHist A))
            (egorovDecodeBHist (egorovEncodeBHist W))
            (egorovDecodeBHist (egorovEncodeBHist U))
            (egorovDecodeBHist (egorovEncodeBHist L))
            (egorovDecodeBHist (egorovEncodeBHist H))
            (egorovDecodeBHist (egorovEncodeBHist C))
            (egorovDecodeBHist (egorovEncodeBHist P))
            (egorovDecodeBHist (egorovEncodeBHist N))) =
          some (EgorovUp.mk M Omega F X S R A W U L H C P N)
      rw [EgorovTasteGate_single_carrier_alignment_decode_encode M,
        EgorovTasteGate_single_carrier_alignment_decode_encode Omega,
        EgorovTasteGate_single_carrier_alignment_decode_encode F,
        EgorovTasteGate_single_carrier_alignment_decode_encode X,
        EgorovTasteGate_single_carrier_alignment_decode_encode S,
        EgorovTasteGate_single_carrier_alignment_decode_encode R,
        EgorovTasteGate_single_carrier_alignment_decode_encode A,
        EgorovTasteGate_single_carrier_alignment_decode_encode W,
        EgorovTasteGate_single_carrier_alignment_decode_encode U,
        EgorovTasteGate_single_carrier_alignment_decode_encode L,
        EgorovTasteGate_single_carrier_alignment_decode_encode H,
        EgorovTasteGate_single_carrier_alignment_decode_encode C,
        EgorovTasteGate_single_carrier_alignment_decode_encode P,
        EgorovTasteGate_single_carrier_alignment_decode_encode N]

private theorem EgorovToEventFlow_injective {x y : EgorovUp} :
    egorovToEventFlow x = egorovToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      egorovFromEventFlow (egorovToEventFlow x) =
        egorovFromEventFlow (egorovToEventFlow y) :=
    congrArg egorovFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EgorovTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EgorovTasteGate_single_carrier_alignment_round_trip y)))

instance egorovBHistCarrier : BHistCarrier EgorovUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := egorovToEventFlow
  fromEventFlow := egorovFromEventFlow

instance egorovChapterTasteGate : ChapterTasteGate EgorovUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change egorovFromEventFlow (egorovToEventFlow x) = some x
    exact EgorovTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EgorovToEventFlow_injective heq)

def taste_gate : ChapterTasteGate EgorovUp :=
  -- BEDC touchpoint anchor: BHist BMark
  egorovChapterTasteGate

theorem EgorovTasteGate_single_carrier_alignment :
    (∀ h : BHist, egorovDecodeBHist (egorovEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EgorovUp) ∧
        Nonempty (ChapterTasteGate EgorovUp) ∧
          egorovEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EgorovTasteGate_single_carrier_alignment_decode_encode,
      ⟨egorovBHistCarrier⟩,
      ⟨egorovChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.EgorovUp
