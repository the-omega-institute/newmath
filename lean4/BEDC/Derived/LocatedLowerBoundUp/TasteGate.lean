import BEDC.Derived.LocatedLowerBoundUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedLowerBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def locatedLowerBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedLowerBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedLowerBoundEncodeBHist h

def locatedLowerBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedLowerBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedLowerBoundDecodeBHist tail)

private theorem locatedLowerBoundDecode_encode :
    ∀ h : BHist, locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedLowerBoundFields : BEDC.Derived.LocatedLowerBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.LocatedLowerBoundUp.mk F L W R E H C P N => [F, L, W, R, E, H, C, P, N]

def locatedLowerBoundToEventFlow : BEDC.Derived.LocatedLowerBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedLowerBoundFields x).map locatedLowerBoundEncodeBHist

private def locatedLowerBoundEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedLowerBoundEventAt index rest

def locatedLowerBoundFromEventFlow (ef : EventFlow) : Option BEDC.Derived.LocatedLowerBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.LocatedLowerBoundUp.mk
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 0 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 1 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 2 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 3 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 4 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 5 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 6 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 7 ef))
      (locatedLowerBoundDecodeBHist (locatedLowerBoundEventAt 8 ef)))

private theorem locatedLowerBound_round_trip :
    ∀ x : BEDC.Derived.LocatedLowerBoundUp,
      locatedLowerBoundFromEventFlow (locatedLowerBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F L W R E H C P N =>
      change
        some
          (BEDC.Derived.LocatedLowerBoundUp.mk
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist F))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist L))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist W))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist R))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist E))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist H))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist C))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist P))
            (locatedLowerBoundDecodeBHist (locatedLowerBoundEncodeBHist N))) =
          some (BEDC.Derived.LocatedLowerBoundUp.mk F L W R E H C P N)
      rw [locatedLowerBoundDecode_encode F, locatedLowerBoundDecode_encode L,
        locatedLowerBoundDecode_encode W, locatedLowerBoundDecode_encode R,
        locatedLowerBoundDecode_encode E, locatedLowerBoundDecode_encode H,
        locatedLowerBoundDecode_encode C, locatedLowerBoundDecode_encode P,
        locatedLowerBoundDecode_encode N]

private theorem locatedLowerBoundToEventFlow_injective
    {x y : BEDC.Derived.LocatedLowerBoundUp} :
    locatedLowerBoundToEventFlow x = locatedLowerBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedLowerBoundFromEventFlow (locatedLowerBoundToEventFlow x) =
        locatedLowerBoundFromEventFlow (locatedLowerBoundToEventFlow y) :=
    congrArg locatedLowerBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedLowerBound_round_trip x).symm
      (Eq.trans hread (locatedLowerBound_round_trip y)))

instance locatedLowerBoundBHistCarrier : BHistCarrier BEDC.Derived.LocatedLowerBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedLowerBoundToEventFlow
  fromEventFlow := locatedLowerBoundFromEventFlow

instance locatedLowerBoundChapterTasteGate :
    ChapterTasteGate BEDC.Derived.LocatedLowerBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedLowerBoundFromEventFlow (locatedLowerBoundToEventFlow x) = some x
    exact locatedLowerBound_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedLowerBoundToEventFlow_injective heq)

theorem LocatedLowerBoundRealSealRoute :
    (∀ x : BEDC.Derived.LocatedLowerBoundUp,
      ∃ F L W R E H C P N : BHist,
        x = BEDC.Derived.LocatedLowerBoundUp.mk F L W R E H C P N ∧
          hsame E E ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N) ∧
      Nonempty (BHistCarrier BEDC.Derived.LocatedLowerBoundUp) ∧
        Nonempty (ChapterTasteGate BEDC.Derived.LocatedLowerBoundUp) := by
  -- BEDC touchpoint anchor: BHist BMark hsame BHistCarrier ChapterTasteGate
  constructor
  · intro x
    cases x with
    | mk F L W R E H C P N =>
        exact
          ⟨F, L, W, R, E, H, C, P, N, rfl, hsame_refl E, hsame_refl H,
            hsame_refl C, hsame_refl P, hsame_refl N⟩
  · exact ⟨⟨locatedLowerBoundBHistCarrier⟩, ⟨locatedLowerBoundChapterTasteGate⟩⟩

end BEDC.Derived.LocatedLowerBoundUp
