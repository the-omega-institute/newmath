import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FourierTransformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FourierTransformUp : Type where
  | mk (W K I R V H C P N : BHist) : FourierTransformUp
  deriving DecidableEq

def fourierTransformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fourierTransformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fourierTransformEncodeBHist h

def fourierTransformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fourierTransformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fourierTransformDecodeBHist tail)

private theorem fourierTransformDecode_encode :
    ∀ h : BHist, fourierTransformDecodeBHist (fourierTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fourierTransformFields : FourierTransformUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FourierTransformUp.mk W K I R V H C P N => [W, K, I, R, V, H, C, P, N]

def fourierTransformToEventFlow : FourierTransformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fourierTransformFields x).map fourierTransformEncodeBHist

private def fourierTransformEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fourierTransformEventAtDefault index rest

def fourierTransformFromEventFlow (ef : EventFlow) : Option FourierTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FourierTransformUp.mk
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 0 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 1 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 2 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 3 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 4 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 5 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 6 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 7 ef))
      (fourierTransformDecodeBHist (fourierTransformEventAtDefault 8 ef)))

private theorem fourierTransform_round_trip :
    ∀ x : FourierTransformUp,
      fourierTransformFromEventFlow (fourierTransformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W K I R V H C P N =>
      change
        some
          (FourierTransformUp.mk
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist W))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist K))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist I))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
            (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) =
          some (FourierTransformUp.mk W K I R V H C P N)
      have hW := fourierTransformDecode_encode W
      have hK := fourierTransformDecode_encode K
      have hI := fourierTransformDecode_encode I
      have hR := fourierTransformDecode_encode R
      have hV := fourierTransformDecode_encode V
      have hH := fourierTransformDecode_encode H
      have hC := fourierTransformDecode_encode C
      have hP := fourierTransformDecode_encode P
      have hN := fourierTransformDecode_encode N
      exact congrArg some
        (calc
          FourierTransformUp.mk
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist W))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist K))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist I))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) =
            FourierTransformUp.mk W
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist K))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist I))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg
                  (fun z => FourierTransformUp.mk z
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist K))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist I))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hW
          _ = FourierTransformUp.mk W K
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist I))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg
                  (fun z => FourierTransformUp.mk W z
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist I))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hK
          _ = FourierTransformUp.mk W K I
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg
                  (fun z => FourierTransformUp.mk W K z
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist R))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hI
          _ = FourierTransformUp.mk W K I R
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg
                  (fun z => FourierTransformUp.mk W K I z
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist V))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hR
          _ = FourierTransformUp.mk W K I R V
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg
                  (fun z => FourierTransformUp.mk W K I R z
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist H))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hV
          _ = FourierTransformUp.mk W K I R V H
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg
                  (fun z => FourierTransformUp.mk W K I R V z
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist C))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hH
          _ = FourierTransformUp.mk W K I R V H C
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg
                  (fun z => FourierTransformUp.mk W K I R V H z
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist P))
                    (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hC
          _ = FourierTransformUp.mk W K I R V H C P
              (fourierTransformDecodeBHist (fourierTransformEncodeBHist N)) :=
                congrArg (fun z => FourierTransformUp.mk W K I R V H C z
                  (fourierTransformDecodeBHist (fourierTransformEncodeBHist N))) hP
          _ = FourierTransformUp.mk W K I R V H C P N :=
                congrArg (FourierTransformUp.mk W K I R V H C P) hN)

private theorem fourierTransformToEventFlow_injective
    {x y : FourierTransformUp} :
    fourierTransformToEventFlow x = fourierTransformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fourierTransformFromEventFlow (fourierTransformToEventFlow x) =
        fourierTransformFromEventFlow (fourierTransformToEventFlow y) :=
    congrArg fourierTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fourierTransform_round_trip x).symm
      (Eq.trans hread (fourierTransform_round_trip y)))

instance fourierTransformBHistCarrier :
    BHistCarrier FourierTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fourierTransformToEventFlow
  fromEventFlow := fourierTransformFromEventFlow

instance fourierTransformChapterTasteGate :
    ChapterTasteGate FourierTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fourierTransformFromEventFlow (fourierTransformToEventFlow x) = some x
    exact fourierTransform_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fourierTransformToEventFlow_injective heq)

instance fourierTransformNontrivial :
    Nontrivial FourierTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FourierTransformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FourierTransformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FourierTransformTasteGate_single_carrier_alignment :
    (forall h : BHist, fourierTransformDecodeBHist (fourierTransformEncodeBHist h) = h) ∧
      (forall x : FourierTransformUp,
        fourierTransformFromEventFlow (fourierTransformToEventFlow x) = some x) ∧
      (forall x y : FourierTransformUp,
        fourierTransformToEventFlow x = fourierTransformToEventFlow y → x = y) ∧
      fourierTransformEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨fourierTransformDecode_encode,
      fourierTransform_round_trip,
      fun _ _ heq => fourierTransformToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.FourierTransformUp
