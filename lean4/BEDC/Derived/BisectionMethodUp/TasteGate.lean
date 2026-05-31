import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BisectionMethodUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BisectionMethodUp : Type where
  | mk (I D L W T S R E H C P N : BHist) : BisectionMethodUp
  deriving DecidableEq

def bisectionMethodEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bisectionMethodEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bisectionMethodEncodeBHist h

def bisectionMethodDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bisectionMethodDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bisectionMethodDecodeBHist tail)

private theorem BisectionMethodTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, bisectionMethodDecodeBHist (bisectionMethodEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bisectionMethodFields : BisectionMethodUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BisectionMethodUp.mk I D L W T S R E H C P N =>
      [I, D, L, W, T, S, R, E, H, C, P, N]

def bisectionMethodToEventFlow : BisectionMethodUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bisectionMethodFields x).map bisectionMethodEncodeBHist

private def bisectionMethodEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bisectionMethodEventAtDefault index rest

def bisectionMethodFromEventFlow (ef : EventFlow) : Option BisectionMethodUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BisectionMethodUp.mk
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 0 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 1 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 2 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 3 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 4 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 5 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 6 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 7 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 8 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 9 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 10 ef))
      (bisectionMethodDecodeBHist (bisectionMethodEventAtDefault 11 ef)))

private theorem BisectionMethodTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BisectionMethodUp,
      bisectionMethodFromEventFlow (bisectionMethodToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D L W T S R E H C P N =>
      change
        some
          (BisectionMethodUp.mk
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist I))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist D))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist L))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist W))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist T))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist S))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist R))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist E))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist H))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist C))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist P))
            (bisectionMethodDecodeBHist (bisectionMethodEncodeBHist N))) =
          some (BisectionMethodUp.mk I D L W T S R E H C P N)
      rw [BisectionMethodTasteGate_single_carrier_alignment_decode I,
        BisectionMethodTasteGate_single_carrier_alignment_decode D,
        BisectionMethodTasteGate_single_carrier_alignment_decode L,
        BisectionMethodTasteGate_single_carrier_alignment_decode W,
        BisectionMethodTasteGate_single_carrier_alignment_decode T,
        BisectionMethodTasteGate_single_carrier_alignment_decode S,
        BisectionMethodTasteGate_single_carrier_alignment_decode R,
        BisectionMethodTasteGate_single_carrier_alignment_decode E,
        BisectionMethodTasteGate_single_carrier_alignment_decode H,
        BisectionMethodTasteGate_single_carrier_alignment_decode C,
        BisectionMethodTasteGate_single_carrier_alignment_decode P,
        BisectionMethodTasteGate_single_carrier_alignment_decode N]

private theorem BisectionMethodTasteGate_single_carrier_alignment_injective
    {x y : BisectionMethodUp} :
    bisectionMethodToEventFlow x = bisectionMethodToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bisectionMethodFromEventFlow (bisectionMethodToEventFlow x) =
        bisectionMethodFromEventFlow (bisectionMethodToEventFlow y) :=
    congrArg bisectionMethodFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BisectionMethodTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BisectionMethodTasteGate_single_carrier_alignment_round_trip y)))

private theorem BisectionMethodTasteGate_single_carrier_alignment_fields :
    ∀ x y : BisectionMethodUp,
      bisectionMethodFields x = bisectionMethodFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 D1 L1 W1 T1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 D2 L2 W2 T2 S2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bisectionMethodBHistCarrier : BHistCarrier BisectionMethodUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bisectionMethodToEventFlow
  fromEventFlow := bisectionMethodFromEventFlow

instance bisectionMethodChapterTasteGate : ChapterTasteGate BisectionMethodUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bisectionMethodFromEventFlow (bisectionMethodToEventFlow x) = some x
    exact BisectionMethodTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BisectionMethodTasteGate_single_carrier_alignment_injective heq)

instance bisectionMethodFieldFaithful : FieldFaithful BisectionMethodUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bisectionMethodFields
  field_faithful := BisectionMethodTasteGate_single_carrier_alignment_fields

instance bisectionMethodNontrivial : Nontrivial BisectionMethodUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BisectionMethodUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BisectionMethodUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BisectionMethodUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bisectionMethodChapterTasteGate

theorem BisectionMethodTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BisectionMethodUp) ∧
      Nonempty (FieldFaithful BisectionMethodUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BisectionMethodUp) ∧
          (∀ h : BHist, bisectionMethodDecodeBHist (bisectionMethodEncodeBHist h) = h) ∧
            (∀ x : BisectionMethodUp,
              bisectionMethodFromEventFlow (bisectionMethodToEventFlow x) =
                some x) ∧
              (∀ x y : BisectionMethodUp,
                bisectionMethodToEventFlow x = bisectionMethodToEventFlow y →
                  x = y) ∧
                bisectionMethodEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro bisectionMethodChapterTasteGate,
      Nonempty.intro bisectionMethodFieldFaithful,
      Nonempty.intro bisectionMethodNontrivial,
      BisectionMethodTasteGate_single_carrier_alignment_decode,
      BisectionMethodTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BisectionMethodTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BisectionMethodUp
