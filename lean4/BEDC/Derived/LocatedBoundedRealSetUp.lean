import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedBoundedRealSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedBoundedRealSetUp : Type where
  | mk (M I D W R E H C P N : BHist) : LocatedBoundedRealSetUp
  deriving DecidableEq

def locatedBoundedRealSetEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedBoundedRealSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedBoundedRealSetEncodeBHist h

def locatedBoundedRealSetDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedBoundedRealSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedBoundedRealSetDecodeBHist tail)

private theorem locatedBoundedRealSetDecodeEncode :
    ∀ h : BHist, locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedBoundedRealSetFields : LocatedBoundedRealSetUp → List BHist
  | LocatedBoundedRealSetUp.mk M I D W R E H C P N => [M, I, D, W, R, E, H, C, P, N]

def locatedBoundedRealSetToEventFlow : LocatedBoundedRealSetUp → EventFlow
  | x => List.map locatedBoundedRealSetEncodeBHist (locatedBoundedRealSetFields x)

private def locatedBoundedRealSetEventAt : Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedBoundedRealSetEventAt index rest

def locatedBoundedRealSetFromEventFlow : EventFlow → Option LocatedBoundedRealSetUp
  | ef =>
      some
        (LocatedBoundedRealSetUp.mk
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 0 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 1 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 2 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 3 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 4 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 5 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 6 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 7 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 8 ef))
          (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEventAt 9 ef)))

private theorem locatedBoundedRealSetRoundTrip :
    ∀ x : LocatedBoundedRealSetUp,
      locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) = some x := by
  intro x
  cases x with
  | mk M I D W R E H C P N =>
      change
        some
          (LocatedBoundedRealSetUp.mk
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist M))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist I))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist D))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist W))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist R))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist E))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist H))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist C))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist P))
            (locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist N))) =
          some (LocatedBoundedRealSetUp.mk M I D W R E H C P N)
      rw [locatedBoundedRealSetDecodeEncode M,
        locatedBoundedRealSetDecodeEncode I,
        locatedBoundedRealSetDecodeEncode D,
        locatedBoundedRealSetDecodeEncode W,
        locatedBoundedRealSetDecodeEncode R,
        locatedBoundedRealSetDecodeEncode E,
        locatedBoundedRealSetDecodeEncode H,
        locatedBoundedRealSetDecodeEncode C,
        locatedBoundedRealSetDecodeEncode P,
        locatedBoundedRealSetDecodeEncode N]

private theorem locatedBoundedRealSetToEventFlowInjective {x y : LocatedBoundedRealSetUp} :
    locatedBoundedRealSetToEventFlow x = locatedBoundedRealSetToEventFlow y → x = y := by
  intro heq
  have hread :
      locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) =
        locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow y) :=
    congrArg locatedBoundedRealSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedBoundedRealSetRoundTrip x).symm
      (Eq.trans hread (locatedBoundedRealSetRoundTrip y)))

private theorem locatedBoundedRealSetFieldFaithful :
    ∀ x y : LocatedBoundedRealSetUp, locatedBoundedRealSetFields x = locatedBoundedRealSetFields y →
      x = y := by
  intro x y hfields
  cases x with
  | mk M1 I1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 I2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedBoundedRealSetBHistCarrier : BHistCarrier LocatedBoundedRealSetUp where
  toEventFlow := locatedBoundedRealSetToEventFlow
  fromEventFlow := locatedBoundedRealSetFromEventFlow

instance locatedBoundedRealSetChapterTasteGate : ChapterTasteGate LocatedBoundedRealSetUp where
  round_trip := by
    intro x
    change locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) = some x
    exact locatedBoundedRealSetRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedBoundedRealSetToEventFlowInjective heq)

instance locatedBoundedRealSetFieldFaithfulInstance : FieldFaithful LocatedBoundedRealSetUp where
  fields := locatedBoundedRealSetFields
  field_faithful := locatedBoundedRealSetFieldFaithful

instance locatedBoundedRealSetNontrivial : Nontrivial LocatedBoundedRealSetUp where
  witness_pair :=
    ⟨LocatedBoundedRealSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedBoundedRealSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedBoundedRealSetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedBoundedRealSetUp) ∧
      Nonempty (FieldFaithful LocatedBoundedRealSetUp) ∧
      Nonempty (Nontrivial LocatedBoundedRealSetUp) ∧
      (∀ h : BHist,
        locatedBoundedRealSetDecodeBHist (locatedBoundedRealSetEncodeBHist h) = h) ∧
      (∀ x : LocatedBoundedRealSetUp,
        locatedBoundedRealSetFromEventFlow (locatedBoundedRealSetToEventFlow x) = some x) ∧
      (∀ x y : LocatedBoundedRealSetUp,
        locatedBoundedRealSetToEventFlow x = locatedBoundedRealSetToEventFlow y → x = y) ∧
      locatedBoundedRealSetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  constructor
  · exact ⟨locatedBoundedRealSetChapterTasteGate⟩
  · constructor
    · exact ⟨locatedBoundedRealSetFieldFaithfulInstance⟩
    · constructor
      · exact ⟨locatedBoundedRealSetNontrivial⟩
      · constructor
        · exact locatedBoundedRealSetDecodeEncode
        · constructor
          · exact locatedBoundedRealSetRoundTrip
          · constructor
            · intro x y heq
              exact locatedBoundedRealSetToEventFlowInjective heq
            · rfl

end BEDC.Derived.LocatedBoundedRealSetUp
