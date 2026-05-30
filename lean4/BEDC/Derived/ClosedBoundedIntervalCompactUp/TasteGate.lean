import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedIntervalCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedIntervalCompactUp : Type where
  | mk (I F U M E H C P N : BHist) : ClosedBoundedIntervalCompactUp
  deriving DecidableEq

def closedBoundedIntervalCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedIntervalCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedIntervalCompactEncodeBHist h

def closedBoundedIntervalCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedIntervalCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedIntervalCompactDecodeBHist tail)

private theorem closedBoundedIntervalCompact_decode_encode :
    ∀ h : BHist,
      closedBoundedIntervalCompactDecodeBHist
          (closedBoundedIntervalCompactEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedBoundedIntervalCompactFields :
    ClosedBoundedIntervalCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedIntervalCompactUp.mk I F U M E H C P N => [I, F, U, M, E, H, C, P, N]

def closedBoundedIntervalCompactToEventFlow :
    ClosedBoundedIntervalCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedBoundedIntervalCompactFields x).map closedBoundedIntervalCompactEncodeBHist

def closedBoundedIntervalCompactFromEventFlow :
    EventFlow → Option ClosedBoundedIntervalCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _I :: [] => none
  | _I :: _F :: [] => none
  | _I :: _F :: _U :: [] => none
  | _I :: _F :: _U :: _M :: [] => none
  | _I :: _F :: _U :: _M :: _E :: [] => none
  | _I :: _F :: _U :: _M :: _E :: _H :: [] => none
  | _I :: _F :: _U :: _M :: _E :: _H :: _C :: [] => none
  | _I :: _F :: _U :: _M :: _E :: _H :: _C :: _P :: [] => none
  | I :: F :: U :: M :: E :: H :: C :: P :: N :: [] =>
      some
        (ClosedBoundedIntervalCompactUp.mk
          (closedBoundedIntervalCompactDecodeBHist I)
          (closedBoundedIntervalCompactDecodeBHist F)
          (closedBoundedIntervalCompactDecodeBHist U)
          (closedBoundedIntervalCompactDecodeBHist M)
          (closedBoundedIntervalCompactDecodeBHist E)
          (closedBoundedIntervalCompactDecodeBHist H)
          (closedBoundedIntervalCompactDecodeBHist C)
          (closedBoundedIntervalCompactDecodeBHist P)
          (closedBoundedIntervalCompactDecodeBHist N))
  | _I :: _F :: _U :: _M :: _E :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem closedBoundedIntervalCompact_round_trip :
    ∀ x : ClosedBoundedIntervalCompactUp,
      closedBoundedIntervalCompactFromEventFlow
          (closedBoundedIntervalCompactToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F U M E H C P N =>
      change
        some
          (ClosedBoundedIntervalCompactUp.mk
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist I))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist F))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist U))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist M))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist E))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist H))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist C))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist P))
            (closedBoundedIntervalCompactDecodeBHist
              (closedBoundedIntervalCompactEncodeBHist N))) =
          some (ClosedBoundedIntervalCompactUp.mk I F U M E H C P N)
      rw [closedBoundedIntervalCompact_decode_encode I,
        closedBoundedIntervalCompact_decode_encode F,
        closedBoundedIntervalCompact_decode_encode U,
        closedBoundedIntervalCompact_decode_encode M,
        closedBoundedIntervalCompact_decode_encode E,
        closedBoundedIntervalCompact_decode_encode H,
        closedBoundedIntervalCompact_decode_encode C,
        closedBoundedIntervalCompact_decode_encode P,
        closedBoundedIntervalCompact_decode_encode N]

private theorem closedBoundedIntervalCompactToEventFlow_injective
    {x y : ClosedBoundedIntervalCompactUp} :
    closedBoundedIntervalCompactToEventFlow x =
        closedBoundedIntervalCompactToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedIntervalCompactFromEventFlow
          (closedBoundedIntervalCompactToEventFlow x) =
        closedBoundedIntervalCompactFromEventFlow
          (closedBoundedIntervalCompactToEventFlow y) :=
    congrArg closedBoundedIntervalCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedBoundedIntervalCompact_round_trip x).symm
      (Eq.trans hread (closedBoundedIntervalCompact_round_trip y)))

instance closedBoundedIntervalCompactBHistCarrier :
    BHistCarrier ClosedBoundedIntervalCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedIntervalCompactToEventFlow
  fromEventFlow := closedBoundedIntervalCompactFromEventFlow

instance closedBoundedIntervalCompactChapterTasteGate :
    ChapterTasteGate ClosedBoundedIntervalCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedBoundedIntervalCompactFromEventFlow
          (closedBoundedIntervalCompactToEventFlow x) =
        some x
    exact closedBoundedIntervalCompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedBoundedIntervalCompactToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ClosedBoundedIntervalCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedBoundedIntervalCompactChapterTasteGate

theorem ClosedBoundedIntervalCompactTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedBoundedIntervalCompactDecodeBHist
          (closedBoundedIntervalCompactEncodeBHist h) =
        h) ∧
      (∀ x : ClosedBoundedIntervalCompactUp,
        closedBoundedIntervalCompactFromEventFlow
            (closedBoundedIntervalCompactToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedBoundedIntervalCompactUp,
          closedBoundedIntervalCompactToEventFlow x =
              closedBoundedIntervalCompactToEventFlow y →
            x = y) ∧
          closedBoundedIntervalCompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨closedBoundedIntervalCompact_decode_encode,
      closedBoundedIntervalCompact_round_trip,
      (fun _ _ heq => closedBoundedIntervalCompactToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ClosedBoundedIntervalCompactUp
