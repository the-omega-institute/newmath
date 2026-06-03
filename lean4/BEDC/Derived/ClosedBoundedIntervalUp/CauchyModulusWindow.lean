import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedIntervalCauchyModulusWindow : Type where
  | mk (L U O D S R E M : BHist) : ClosedBoundedIntervalCauchyModulusWindow
  deriving DecidableEq

def closedBoundedIntervalCauchyModulusWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedIntervalCauchyModulusWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedIntervalCauchyModulusWindowEncodeBHist h

def closedBoundedIntervalCauchyModulusWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedIntervalCauchyModulusWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedIntervalCauchyModulusWindowDecodeBHist tail)

private theorem
    ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      closedBoundedIntervalCauchyModulusWindowDecodeBHist
        (closedBoundedIntervalCauchyModulusWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedBoundedIntervalCauchyModulusWindowToEventFlow :
    ClosedBoundedIntervalCauchyModulusWindow → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedIntervalCauchyModulusWindow.mk L U O D S R E M =>
      [closedBoundedIntervalCauchyModulusWindowEncodeBHist L,
        closedBoundedIntervalCauchyModulusWindowEncodeBHist U,
        closedBoundedIntervalCauchyModulusWindowEncodeBHist O,
        closedBoundedIntervalCauchyModulusWindowEncodeBHist D,
        closedBoundedIntervalCauchyModulusWindowEncodeBHist S,
        closedBoundedIntervalCauchyModulusWindowEncodeBHist R,
        closedBoundedIntervalCauchyModulusWindowEncodeBHist E,
        closedBoundedIntervalCauchyModulusWindowEncodeBHist M]

def closedBoundedIntervalCauchyModulusWindowFromEventFlow :
    EventFlow → Option ClosedBoundedIntervalCauchyModulusWindow
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restL =>
      match restL with
      | [] => none
      | U :: restU =>
          match restU with
          | [] => none
          | O :: restO =>
              match restO with
              | [] => none
              | D :: restD =>
                  match restD with
                  | [] => none
                  | S :: restS =>
                      match restS with
                      | [] => none
                      | R :: restR =>
                          match restR with
                          | [] => none
                          | E :: restE =>
                              match restE with
                              | [] => none
                              | M :: restM =>
                                  match restM with
                                  | [] =>
                                      some
                                        (ClosedBoundedIntervalCauchyModulusWindow.mk
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist L)
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist U)
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist O)
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist D)
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist S)
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist R)
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist E)
                                          (closedBoundedIntervalCauchyModulusWindowDecodeBHist M))
                                  | _ :: _ => none

private theorem
    ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_round_trip :
    ∀ x : ClosedBoundedIntervalCauchyModulusWindow,
      closedBoundedIntervalCauchyModulusWindowFromEventFlow
        (closedBoundedIntervalCauchyModulusWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U O D S R E M =>
      change
        some
          (ClosedBoundedIntervalCauchyModulusWindow.mk
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist L))
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist U))
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist O))
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist D))
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist S))
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist R))
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist E))
            (closedBoundedIntervalCauchyModulusWindowDecodeBHist
              (closedBoundedIntervalCauchyModulusWindowEncodeBHist M))) =
          some (ClosedBoundedIntervalCauchyModulusWindow.mk L U O D S R E M)
      rw [ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode L,
        ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode U,
        ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode O,
        ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode D,
        ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode S,
        ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode R,
        ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode E,
        ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode M]

private theorem ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_injective
    {x y : ClosedBoundedIntervalCauchyModulusWindow} :
    closedBoundedIntervalCauchyModulusWindowToEventFlow x =
      closedBoundedIntervalCauchyModulusWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedIntervalCauchyModulusWindowFromEventFlow
          (closedBoundedIntervalCauchyModulusWindowToEventFlow x) =
        closedBoundedIntervalCauchyModulusWindowFromEventFlow
          (closedBoundedIntervalCauchyModulusWindowToEventFlow y) :=
    congrArg closedBoundedIntervalCauchyModulusWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_round_trip y)))

instance closedBoundedIntervalCauchyModulusWindowBHistCarrier :
    BHistCarrier ClosedBoundedIntervalCauchyModulusWindow where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedIntervalCauchyModulusWindowToEventFlow
  fromEventFlow := closedBoundedIntervalCauchyModulusWindowFromEventFlow

instance closedBoundedIntervalCauchyModulusWindowChapterTasteGate :
    ChapterTasteGate ClosedBoundedIntervalCauchyModulusWindow where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedBoundedIntervalCauchyModulusWindowFromEventFlow
        (closedBoundedIntervalCauchyModulusWindowToEventFlow x) = some x
    exact ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_injective heq)

theorem ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment :
    (forall h : BHist,
      closedBoundedIntervalCauchyModulusWindowDecodeBHist
        (closedBoundedIntervalCauchyModulusWindowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ClosedBoundedIntervalCauchyModulusWindow) ∧
        Nonempty (ChapterTasteGate ClosedBoundedIntervalCauchyModulusWindow) ∧
          closedBoundedIntervalCauchyModulusWindowEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ClosedBoundedIntervalCauchyModulusWindow_single_carrier_alignment_decode_encode,
      ⟨closedBoundedIntervalCauchyModulusWindowBHistCarrier⟩,
      ⟨closedBoundedIntervalCauchyModulusWindowChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ClosedboundedintervalUp
