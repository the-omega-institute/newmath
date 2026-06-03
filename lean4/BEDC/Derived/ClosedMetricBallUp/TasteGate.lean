import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedMetricBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedMetricBallUp : Type where
  | mk (M X c r rho D R S Q H C P N : BHist) : ClosedMetricBallUp
  deriving DecidableEq

def closedMetricBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedMetricBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedMetricBallEncodeBHist h

def closedMetricBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedMetricBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedMetricBallDecodeBHist tail)

private theorem ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, closedMetricBallDecodeBHist (closedMetricBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem ClosedMetricBallTasteGate_single_carrier_alignment_mk_congr
    {M M' X X' c c' r r' rho rho' D D' R R' S S' Q Q' H H' C C' P P' N N' :
      BHist}
    (hM : M' = M)
    (hX : X' = X)
    (hc : c' = c)
    (hr : r' = r)
    (hrho : rho' = rho)
    (hD : D' = D)
    (hR : R' = R)
    (hS : S' = S)
    (hQ : Q' = Q)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    ClosedMetricBallUp.mk M' X' c' r' rho' D' R' S' Q' H' C' P' N' =
      ClosedMetricBallUp.mk M X c r rho D R S Q H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hX
  cases hc
  cases hr
  cases hrho
  cases hD
  cases hR
  cases hS
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def closedMetricBallToEventFlow : ClosedMetricBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedMetricBallUp.mk M X c r rho D R S Q H C P N =>
      [closedMetricBallEncodeBHist M,
        closedMetricBallEncodeBHist X,
        closedMetricBallEncodeBHist c,
        closedMetricBallEncodeBHist r,
        closedMetricBallEncodeBHist rho,
        closedMetricBallEncodeBHist D,
        closedMetricBallEncodeBHist R,
        closedMetricBallEncodeBHist S,
        closedMetricBallEncodeBHist Q,
        closedMetricBallEncodeBHist H,
        closedMetricBallEncodeBHist C,
        closedMetricBallEncodeBHist P,
        closedMetricBallEncodeBHist N]

private def closedMetricBallEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedMetricBallEventAtDefault index rest

def closedMetricBallFromEventFlow (ef : EventFlow) : Option ClosedMetricBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedMetricBallUp.mk
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 0 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 1 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 2 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 3 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 4 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 5 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 6 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 7 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 8 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 9 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 10 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 11 ef))
      (closedMetricBallDecodeBHist (closedMetricBallEventAtDefault 12 ef)))

private theorem ClosedMetricBallTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedMetricBallUp,
      closedMetricBallFromEventFlow (closedMetricBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M X c r rho D R S Q H C P N =>
      exact
        congrArg some
          (ClosedMetricBallTasteGate_single_carrier_alignment_mk_congr
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode M)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode X)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode c)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode r)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode rho)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode D)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode R)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode S)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode Q)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode H)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode C)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode P)
            (ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode N))

private theorem ClosedMetricBallTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedMetricBallUp} :
    closedMetricBallToEventFlow x = closedMetricBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedMetricBallFromEventFlow (closedMetricBallToEventFlow x) =
        closedMetricBallFromEventFlow (closedMetricBallToEventFlow y) :=
    congrArg closedMetricBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedMetricBallTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClosedMetricBallTasteGate_single_carrier_alignment_round_trip y)))

instance closedMetricBallBHistCarrier : BHistCarrier ClosedMetricBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedMetricBallToEventFlow
  fromEventFlow := closedMetricBallFromEventFlow

instance closedMetricBallChapterTasteGate : ChapterTasteGate ClosedMetricBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedMetricBallFromEventFlow (closedMetricBallToEventFlow x) = some x
    exact ClosedMetricBallTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedMetricBallTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ClosedMetricBallTasteGate_single_carrier_alignment :
    (forall h : BHist, closedMetricBallDecodeBHist (closedMetricBallEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ClosedMetricBallUp) ∧
        Nonempty (ChapterTasteGate ClosedMetricBallUp) ∧
          closedMetricBallEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ClosedMetricBallTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro closedMetricBallBHistCarrier,
      Nonempty.intro closedMetricBallChapterTasteGate,
      rfl⟩

end BEDC.Derived.ClosedMetricBallUp
