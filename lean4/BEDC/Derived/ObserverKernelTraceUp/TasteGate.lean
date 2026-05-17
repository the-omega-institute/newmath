import BEDC.FKernel.Mark
import BEDC.Derived.ObserverKernelTraceUp
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverKernelTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def observerKernelTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerKernelTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerKernelTraceEncodeBHist h

def observerKernelTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerKernelTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerKernelTraceDecodeBHist tail)

private theorem observerKernelTraceDecode_encode_bhist :
    ∀ h : BHist, observerKernelTraceDecodeBHist (observerKernelTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem observerKernelTrace_mk_congr
    {T T' H H' C C' B B' S S' L L' P P' N N' : BHist}
    (hT : T' = T) (hH : H' = H) (hC : C' = C) (hB : B' = B) (hS : S' = S)
    (hL : L' = L) (hP : P' = P) (hN : N' = N) :
    ObserverKernelTraceUp.mk T' H' C' B' S' L' P' N' =
      ObserverKernelTraceUp.mk T H C B S L P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hH
  cases hC
  cases hB
  cases hS
  cases hL
  cases hP
  cases hN
  rfl

def observerKernelTraceFields : ObserverKernelTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverKernelTraceUp.mk T H C B S L P N => [T, H, C, B, S, L, P, N]

def observerKernelTraceToEventFlow : ObserverKernelTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (observerKernelTraceFields x).map observerKernelTraceEncodeBHist

def observerKernelTraceFromEventFlow :
    EventFlow → Option ObserverKernelTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _T :: [] => none
  | _T :: _H :: [] => none
  | _T :: _H :: _C :: [] => none
  | _T :: _H :: _C :: _B :: [] => none
  | _T :: _H :: _C :: _B :: _S :: [] => none
  | _T :: _H :: _C :: _B :: _S :: _L :: [] => none
  | _T :: _H :: _C :: _B :: _S :: _L :: _P :: [] => none
  | T :: H :: C :: B :: S :: L :: P :: N :: [] =>
      some
        (ObserverKernelTraceUp.mk
          (observerKernelTraceDecodeBHist T)
          (observerKernelTraceDecodeBHist H)
          (observerKernelTraceDecodeBHist C)
          (observerKernelTraceDecodeBHist B)
          (observerKernelTraceDecodeBHist S)
          (observerKernelTraceDecodeBHist L)
          (observerKernelTraceDecodeBHist P)
          (observerKernelTraceDecodeBHist N))
  | _T :: _H :: _C :: _B :: _S :: _L :: _P :: _N :: _extra :: _rest => none

private theorem observerKernelTrace_round_trip :
    ∀ x : ObserverKernelTraceUp,
      observerKernelTraceFromEventFlow (observerKernelTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T H C B S L P N =>
      exact
        congrArg some
          (observerKernelTrace_mk_congr
            (observerKernelTraceDecode_encode_bhist T)
            (observerKernelTraceDecode_encode_bhist H)
            (observerKernelTraceDecode_encode_bhist C)
            (observerKernelTraceDecode_encode_bhist B)
            (observerKernelTraceDecode_encode_bhist S)
            (observerKernelTraceDecode_encode_bhist L)
            (observerKernelTraceDecode_encode_bhist P)
            (observerKernelTraceDecode_encode_bhist N))

private theorem observerKernelTraceToEventFlow_injective
    {x y : ObserverKernelTraceUp} :
    observerKernelTraceToEventFlow x = observerKernelTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerKernelTraceFromEventFlow (observerKernelTraceToEventFlow x) =
        observerKernelTraceFromEventFlow (observerKernelTraceToEventFlow y) :=
    congrArg observerKernelTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerKernelTrace_round_trip x).symm
      (Eq.trans hread (observerKernelTrace_round_trip y)))

private theorem observerKernelTrace_field_faithful :
    ∀ x y : ObserverKernelTraceUp,
      observerKernelTraceFields x = observerKernelTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T H C B S L P N =>
      cases y with
      | mk T' H' C' B' S' L' P' N' =>
          cases hfields
          rfl

instance observerKernelTraceBHistCarrier : BHistCarrier ObserverKernelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerKernelTraceToEventFlow
  fromEventFlow := observerKernelTraceFromEventFlow

instance observerKernelTraceChapterTasteGate : ChapterTasteGate ObserverKernelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerKernelTraceFromEventFlow (observerKernelTraceToEventFlow x) = some x
    exact observerKernelTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerKernelTraceToEventFlow_injective heq)

instance observerKernelTraceFieldFaithful : FieldFaithful ObserverKernelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerKernelTraceFields
  field_faithful := observerKernelTrace_field_faithful

instance observerKernelTraceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ObserverKernelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverKernelTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverKernelTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverKernelTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerKernelTraceChapterTasteGate

theorem ObserverKernelTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerKernelTraceDecodeBHist (observerKernelTraceEncodeBHist h) = h) ∧
      (∀ x : ObserverKernelTraceUp,
        observerKernelTraceFromEventFlow (observerKernelTraceToEventFlow x) = some x) ∧
        (∀ x y : ObserverKernelTraceUp,
          observerKernelTraceToEventFlow x = observerKernelTraceToEventFlow y → x = y) ∧
          observerKernelTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨observerKernelTraceDecode_encode_bhist,
      observerKernelTrace_round_trip,
      (fun _ _ heq => observerKernelTraceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ObserverKernelTraceUp
