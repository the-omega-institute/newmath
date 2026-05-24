import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyShuffleUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyShuffleUp : Type where
  | mk (A B S E O D RA RB LA LB H C P N : BHist) : RegularCauchyShuffleUp
  deriving DecidableEq

def regularCauchyShuffleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyShuffleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyShuffleEncodeBHist h

def regularCauchyShuffleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyShuffleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyShuffleDecodeBHist tail)

private theorem RegularCauchyShuffleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyShuffleFields : RegularCauchyShuffleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyShuffleUp.mk A B S E O D RA RB LA LB H C P N =>
      [A, B, S, E, O, D, RA, RB, LA, LB, H, C, P, N]

def regularCauchyShuffleToEventFlow : RegularCauchyShuffleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyShuffleFields x).map regularCauchyShuffleEncodeBHist

private def regularCauchyShuffleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyShuffleEventAtDefault index rest

def regularCauchyShuffleFromEventFlow
    (ef : EventFlow) : Option RegularCauchyShuffleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyShuffleUp.mk
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 0 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 1 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 2 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 3 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 4 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 5 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 6 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 7 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 8 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 9 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 10 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 11 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 12 ef))
      (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEventAtDefault 13 ef)))

private theorem RegularCauchyShuffleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyShuffleUp,
      regularCauchyShuffleFromEventFlow (regularCauchyShuffleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk A B S E O D RA RB LA LB H C P N =>
      change
        some
          (RegularCauchyShuffleUp.mk
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist A))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist B))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist S))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist E))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist O))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist D))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist RA))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist RB))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist LA))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist LB))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist H))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist C))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist P))
            (regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist N))) =
          some (RegularCauchyShuffleUp.mk A B S E O D RA RB LA LB H C P N)
      rw [RegularCauchyShuffleTasteGate_single_carrier_alignment_decode A,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode B,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode S,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode E,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode O,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode D,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode RA,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode RB,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode LA,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode LB,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode H,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode C,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode P,
        RegularCauchyShuffleTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyShuffleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyShuffleUp} :
    regularCauchyShuffleToEventFlow x = regularCauchyShuffleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyShuffleFromEventFlow (regularCauchyShuffleToEventFlow x) =
        regularCauchyShuffleFromEventFlow (regularCauchyShuffleToEventFlow y) :=
    congrArg regularCauchyShuffleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyShuffleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyShuffleTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyShuffleBHistCarrier : BHistCarrier RegularCauchyShuffleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyShuffleToEventFlow
  fromEventFlow := regularCauchyShuffleFromEventFlow

instance regularCauchyShuffleChapterTasteGate :
    ChapterTasteGate RegularCauchyShuffleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyShuffleFromEventFlow (regularCauchyShuffleToEventFlow x) = some x
    exact RegularCauchyShuffleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyShuffleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyShuffleFieldFaithful : FieldFaithful RegularCauchyShuffleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyShuffleFields
  field_faithful := by
    intro x y h
    exact RegularCauchyShuffleTasteGate_single_carrier_alignment_toEventFlow_injective
      (congrArg (List.map regularCauchyShuffleEncodeBHist) h)

instance regularCauchyShuffleNontrivial : Nontrivial RegularCauchyShuffleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyShuffleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyShuffleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyShuffleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyShuffleChapterTasteGate

theorem RegularCauchyShuffleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyShuffleDecodeBHist (regularCauchyShuffleEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyShuffleUp,
        regularCauchyShuffleFromEventFlow (regularCauchyShuffleToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyShuffleUp,
          regularCauchyShuffleToEventFlow x = regularCauchyShuffleToEventFlow y -> x = y) ∧
          regularCauchyShuffleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyShuffleTasteGate_single_carrier_alignment_decode,
      RegularCauchyShuffleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyShuffleTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

theorem RegularCauchyShuffleEvenOddProjectionHandoff
    (x : RegularCauchyShuffleUp) :
    ∃ A B S E O D RA RB LA LB H C P N evenRead oddRead evenSeal oddSeal : BHist,
      x = RegularCauchyShuffleUp.mk A B S E O D RA RB LA LB H C P N ∧
        regularCauchyShuffleFields x = [A, B, S, E, O, D, RA, RB, LA, LB, H, C, P, N] ∧
          Cont S E evenRead ∧ Cont evenRead RA evenSeal ∧ Cont S O oddRead ∧
            Cont oddRead RB oddSeal := by
  -- BEDC touchpoint anchor: BHist Cont append RegularCauchyShuffleUp
  cases x with
  | mk A B S E O D RA RB LA LB H C P N =>
      exact
        ⟨A, B, S, E, O, D, RA, RB, LA, LB, H, C, P, N, append S E, append S O,
          append (append S E) RA, append (append S O) RB, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.RegularCauchyShuffleUp
