import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicNestedIntervalSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicNestedIntervalSelectorUp : Type where
  | mk (I D S R E H C P N : BHist) : DyadicNestedIntervalSelectorUp
  deriving DecidableEq

def dyadicNestedIntervalSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicNestedIntervalSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicNestedIntervalSelectorEncodeBHist h

def dyadicNestedIntervalSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicNestedIntervalSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicNestedIntervalSelectorDecodeBHist tail)

private theorem dyadicNestedIntervalSelectorDecode_encode :
    ∀ h : BHist,
      dyadicNestedIntervalSelectorDecodeBHist
          (dyadicNestedIntervalSelectorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicNestedIntervalSelectorToEventFlow :
    DyadicNestedIntervalSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicNestedIntervalSelectorUp.mk I D S R E H C P N =>
      [dyadicNestedIntervalSelectorEncodeBHist I,
        dyadicNestedIntervalSelectorEncodeBHist D,
        dyadicNestedIntervalSelectorEncodeBHist S,
        dyadicNestedIntervalSelectorEncodeBHist R,
        dyadicNestedIntervalSelectorEncodeBHist E,
        dyadicNestedIntervalSelectorEncodeBHist H,
        dyadicNestedIntervalSelectorEncodeBHist C,
        dyadicNestedIntervalSelectorEncodeBHist P,
        dyadicNestedIntervalSelectorEncodeBHist N]

def dyadicNestedIntervalSelectorFromEventFlow :
    EventFlow → Option DyadicNestedIntervalSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restD =>
      match restD with
      | [] => none
      | D :: restS =>
          match restS with
          | [] => none
          | S :: restR =>
              match restR with
              | [] => none
              | R :: restE =>
                  match restE with
                  | [] => none
                  | E :: restH =>
                      match restH with
                      | [] => none
                      | H :: restC =>
                          match restC with
                          | [] => none
                          | C :: restP =>
                              match restP with
                              | [] => none
                              | P :: restN =>
                                  match restN with
                                  | [] => none
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (DyadicNestedIntervalSelectorUp.mk
                                              (dyadicNestedIntervalSelectorDecodeBHist I)
                                              (dyadicNestedIntervalSelectorDecodeBHist D)
                                              (dyadicNestedIntervalSelectorDecodeBHist S)
                                              (dyadicNestedIntervalSelectorDecodeBHist R)
                                              (dyadicNestedIntervalSelectorDecodeBHist E)
                                              (dyadicNestedIntervalSelectorDecodeBHist H)
                                              (dyadicNestedIntervalSelectorDecodeBHist C)
                                              (dyadicNestedIntervalSelectorDecodeBHist P)
                                              (dyadicNestedIntervalSelectorDecodeBHist N))
                                      | _ :: _ => none

private theorem dyadicNestedIntervalSelector_round_trip :
    ∀ x : DyadicNestedIntervalSelectorUp,
      dyadicNestedIntervalSelectorFromEventFlow
          (dyadicNestedIntervalSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D S R E H C P N =>
      change
        some
          (DyadicNestedIntervalSelectorUp.mk
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist I))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist D))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist S))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist R))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist E))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist H))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist C))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist P))
            (dyadicNestedIntervalSelectorDecodeBHist
              (dyadicNestedIntervalSelectorEncodeBHist N))) =
          some (DyadicNestedIntervalSelectorUp.mk I D S R E H C P N)
      rw [dyadicNestedIntervalSelectorDecode_encode I,
        dyadicNestedIntervalSelectorDecode_encode D,
        dyadicNestedIntervalSelectorDecode_encode S,
        dyadicNestedIntervalSelectorDecode_encode R,
        dyadicNestedIntervalSelectorDecode_encode E,
        dyadicNestedIntervalSelectorDecode_encode H,
        dyadicNestedIntervalSelectorDecode_encode C,
        dyadicNestedIntervalSelectorDecode_encode P,
        dyadicNestedIntervalSelectorDecode_encode N]

private theorem dyadicNestedIntervalSelectorToEventFlow_injective
    {x y : DyadicNestedIntervalSelectorUp} :
    dyadicNestedIntervalSelectorToEventFlow x =
        dyadicNestedIntervalSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicNestedIntervalSelectorFromEventFlow
          (dyadicNestedIntervalSelectorToEventFlow x) =
        dyadicNestedIntervalSelectorFromEventFlow
          (dyadicNestedIntervalSelectorToEventFlow y) :=
    congrArg dyadicNestedIntervalSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicNestedIntervalSelector_round_trip x).symm
      (Eq.trans hread (dyadicNestedIntervalSelector_round_trip y)))

instance dyadicNestedIntervalSelectorBHistCarrier :
    BHistCarrier DyadicNestedIntervalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicNestedIntervalSelectorToEventFlow
  fromEventFlow := dyadicNestedIntervalSelectorFromEventFlow

instance dyadicNestedIntervalSelectorChapterTasteGate :
    ChapterTasteGate DyadicNestedIntervalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicNestedIntervalSelectorFromEventFlow
          (dyadicNestedIntervalSelectorToEventFlow x) =
        some x
    exact dyadicNestedIntervalSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicNestedIntervalSelectorToEventFlow_injective heq)

theorem DyadicNestedIntervalSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicNestedIntervalSelectorDecodeBHist
          (dyadicNestedIntervalSelectorEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier DyadicNestedIntervalSelectorUp) ∧
        Nonempty (ChapterTasteGate DyadicNestedIntervalSelectorUp) ∧
          dyadicNestedIntervalSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dyadicNestedIntervalSelectorDecode_encode,
      ⟨{
        toEventFlow := dyadicNestedIntervalSelectorToEventFlow
        fromEventFlow := dyadicNestedIntervalSelectorFromEventFlow
      }⟩,
      ⟨{
        round_trip := by
          intro x
          change
            dyadicNestedIntervalSelectorFromEventFlow
                (dyadicNestedIntervalSelectorToEventFlow x) =
              some x
          exact dyadicNestedIntervalSelector_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (dyadicNestedIntervalSelectorToEventFlow_injective heq)
      }⟩,
      rfl⟩

end BEDC.Derived.DyadicNestedIntervalSelectorUp
