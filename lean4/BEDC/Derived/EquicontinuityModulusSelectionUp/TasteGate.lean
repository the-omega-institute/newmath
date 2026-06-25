import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuityModulusSelectionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuityModulusSelectionUp : Type where
  | mk (K E Q M U R H C P N : BHist) : EquicontinuityModulusSelectionUp
  deriving DecidableEq

def equicontinuityModulusSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuityModulusSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuityModulusSelectionEncodeBHist h

def equicontinuityModulusSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuityModulusSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuityModulusSelectionDecodeBHist tail)

private theorem equicontinuityModulusSelectionDecode_encode :
    ∀ h : BHist,
      equicontinuityModulusSelectionDecodeBHist
          (equicontinuityModulusSelectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuityModulusSelectionFields :
    EquicontinuityModulusSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuityModulusSelectionUp.mk K E Q M U R H C P N =>
      [K, E, Q, M, U, R, H, C, P, N]

def equicontinuityModulusSelectionToEventFlow :
    EquicontinuityModulusSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (equicontinuityModulusSelectionFields x).map
      equicontinuityModulusSelectionEncodeBHist

private def equicontinuityModulusSelectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      equicontinuityModulusSelectionEventAt index rest

def equicontinuityModulusSelectionFromEventFlow
    (ef : EventFlow) : Option EquicontinuityModulusSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EquicontinuityModulusSelectionUp.mk
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 0 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 1 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 2 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 3 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 4 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 5 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 6 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 7 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 8 ef))
      (equicontinuityModulusSelectionDecodeBHist
        (equicontinuityModulusSelectionEventAt 9 ef)))

private theorem equicontinuityModulusSelection_round_trip :
    ∀ x : EquicontinuityModulusSelectionUp,
      equicontinuityModulusSelectionFromEventFlow
          (equicontinuityModulusSelectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K E Q M U R H C P N =>
      change
        some
          (EquicontinuityModulusSelectionUp.mk
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist K))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist E))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist Q))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist M))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist U))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist R))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist H))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist C))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist P))
            (equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist N))) =
          some (EquicontinuityModulusSelectionUp.mk K E Q M U R H C P N)
      rw [equicontinuityModulusSelectionDecode_encode K,
        equicontinuityModulusSelectionDecode_encode E,
        equicontinuityModulusSelectionDecode_encode Q,
        equicontinuityModulusSelectionDecode_encode M,
        equicontinuityModulusSelectionDecode_encode U,
        equicontinuityModulusSelectionDecode_encode R,
        equicontinuityModulusSelectionDecode_encode H,
        equicontinuityModulusSelectionDecode_encode C,
        equicontinuityModulusSelectionDecode_encode P,
        equicontinuityModulusSelectionDecode_encode N]

private theorem equicontinuityModulusSelectionToEventFlow_injective
    {x y : EquicontinuityModulusSelectionUp} :
    equicontinuityModulusSelectionToEventFlow x =
        equicontinuityModulusSelectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuityModulusSelectionFromEventFlow
          (equicontinuityModulusSelectionToEventFlow x) =
        equicontinuityModulusSelectionFromEventFlow
          (equicontinuityModulusSelectionToEventFlow y) :=
    congrArg equicontinuityModulusSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (equicontinuityModulusSelection_round_trip x).symm
      (Eq.trans hread (equicontinuityModulusSelection_round_trip y)))

instance equicontinuityModulusSelectionBHistCarrier :
    BHistCarrier EquicontinuityModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuityModulusSelectionToEventFlow
  fromEventFlow := equicontinuityModulusSelectionFromEventFlow

instance equicontinuityModulusSelectionChapterTasteGate :
    ChapterTasteGate EquicontinuityModulusSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      equicontinuityModulusSelectionFromEventFlow
          (equicontinuityModulusSelectionToEventFlow x) =
        some x
    exact equicontinuityModulusSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (equicontinuityModulusSelectionToEventFlow_injective heq)

theorem EquicontinuityModulusSelectionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier EquicontinuityModulusSelectionUp) ∧
      Nonempty (ChapterTasteGate EquicontinuityModulusSelectionUp) ∧
        (∀ h : BHist,
          equicontinuityModulusSelectionDecodeBHist
              (equicontinuityModulusSelectionEncodeBHist h) =
            h) ∧
          (∀ x : EquicontinuityModulusSelectionUp,
            equicontinuityModulusSelectionFromEventFlow
                (equicontinuityModulusSelectionToEventFlow x) =
              some x) ∧
            equicontinuityModulusSelectionEncodeBHist BHist.Empty =
              ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨equicontinuityModulusSelectionBHistCarrier⟩,
      ⟨equicontinuityModulusSelectionChapterTasteGate⟩,
      equicontinuityModulusSelectionDecode_encode,
      equicontinuityModulusSelection_round_trip,
      rfl⟩

end BEDC.Derived.EquicontinuityModulusSelectionUp.TasteGate
