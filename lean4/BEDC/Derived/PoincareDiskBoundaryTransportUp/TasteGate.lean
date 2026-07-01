import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareDiskBoundaryTransportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareDiskBoundaryTransportUp : Type where
  | mk (D B M T F H C P N : BHist) : PoincareDiskBoundaryTransportUp
  deriving DecidableEq

def poincareDiskBoundaryTransportEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareDiskBoundaryTransportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareDiskBoundaryTransportEncodeBHist h

def poincareDiskBoundaryTransportDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareDiskBoundaryTransportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareDiskBoundaryTransportDecodeBHist tail)

private theorem PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      poincareDiskBoundaryTransportDecodeBHist
          (poincareDiskBoundaryTransportEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def poincareDiskBoundaryTransportFields :
    PoincareDiskBoundaryTransportUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareDiskBoundaryTransportUp.mk D B M T F H C P N => [D, B, M, T, F, H, C, P, N]

def poincareDiskBoundaryTransportToEventFlow :
    PoincareDiskBoundaryTransportUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poincareDiskBoundaryTransportFields x).map
      poincareDiskBoundaryTransportEncodeBHist

private def poincareDiskBoundaryTransportEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => poincareDiskBoundaryTransportEventAt index rest

def poincareDiskBoundaryTransportFromEventFlow :
    EventFlow -> Option PoincareDiskBoundaryTransportUp
  -- BEDC touchpoint anchor: BHist BMark
  | eventFlow =>
      some
        (PoincareDiskBoundaryTransportUp.mk
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 0 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 1 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 2 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 3 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 4 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 5 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 6 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 7 eventFlow))
          (poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEventAt 8 eventFlow)))

private theorem PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_round_trip :
    forall x : PoincareDiskBoundaryTransportUp,
      poincareDiskBoundaryTransportFromEventFlow
          (poincareDiskBoundaryTransportToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D B M T F H C P N =>
      change
        some
            (PoincareDiskBoundaryTransportUp.mk
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist D))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist B))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist M))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist T))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist F))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist H))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist C))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist P))
              (poincareDiskBoundaryTransportDecodeBHist
                (poincareDiskBoundaryTransportEncodeBHist N))) =
          some (PoincareDiskBoundaryTransportUp.mk D B M T F H C P N)
      rw [PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode D,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode B,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode M,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode T,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode F,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode H,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode C,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode P,
        PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode N]

private theorem PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PoincareDiskBoundaryTransportUp} :
    poincareDiskBoundaryTransportToEventFlow x =
        poincareDiskBoundaryTransportToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareDiskBoundaryTransportFromEventFlow
          (poincareDiskBoundaryTransportToEventFlow x) =
        poincareDiskBoundaryTransportFromEventFlow
          (poincareDiskBoundaryTransportToEventFlow y) :=
    congrArg poincareDiskBoundaryTransportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_round_trip y)))

instance poincareDiskBoundaryTransportBHistCarrier :
    BHistCarrier PoincareDiskBoundaryTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareDiskBoundaryTransportToEventFlow
  fromEventFlow := poincareDiskBoundaryTransportFromEventFlow

instance poincareDiskBoundaryTransportChapterTasteGate :
    ChapterTasteGate PoincareDiskBoundaryTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      poincareDiskBoundaryTransportFromEventFlow
          (poincareDiskBoundaryTransportToEventFlow x) =
        some x
    exact PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment :
    (forall h : BHist,
        poincareDiskBoundaryTransportDecodeBHist
            (poincareDiskBoundaryTransportEncodeBHist h) =
          h) ∧
      (forall x : PoincareDiskBoundaryTransportUp,
        poincareDiskBoundaryTransportFromEventFlow
            (poincareDiskBoundaryTransportToEventFlow x) =
          some x) ∧
        Nonempty (BHistCarrier PoincareDiskBoundaryTransportUp) ∧
          Nonempty (ChapterTasteGate PoincareDiskBoundaryTransportUp) ∧
            poincareDiskBoundaryTransportEncodeBHist BHist.Empty =
              ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_decode,
      PoincareDiskBoundaryTransportTasteGate_single_carrier_alignment_round_trip,
      ⟨poincareDiskBoundaryTransportBHistCarrier⟩,
      ⟨poincareDiskBoundaryTransportChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PoincareDiskBoundaryTransportUp
