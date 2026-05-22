import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionSplitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionSplitUp : Type where
  | mk (X U V A I G W D R E H C P N : BHist) : CauchyCompletionSplitUp
  deriving DecidableEq

def cauchyCompletionSplitEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionSplitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionSplitEncodeBHist h

def cauchyCompletionSplitDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionSplitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionSplitDecodeBHist tail)

private theorem cauchyCompletionSplitDecodeEncodeBHist :
    forall h : BHist,
      cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionSplitFields : CauchyCompletionSplitUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionSplitUp.mk X U V A I G W D R E H C P N =>
      [X, U, V, A, I, G, W, D, R, E, H, C, P, N]

def cauchyCompletionSplitToEventFlow : CauchyCompletionSplitUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionSplitFields x).map cauchyCompletionSplitEncodeBHist

private def cauchyCompletionSplitEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionSplitEventAtDefault index rest

def cauchyCompletionSplitFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionSplitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionSplitUp.mk
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 0 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 1 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 2 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 3 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 4 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 5 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 6 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 7 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 8 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 9 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 10 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 11 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 12 ef))
      (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEventAtDefault 13 ef)))

private theorem cauchyCompletionSplitRoundTrip :
    forall x : CauchyCompletionSplitUp,
      cauchyCompletionSplitFromEventFlow (cauchyCompletionSplitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U V A I G W D R E H C P N =>
      change
        some
          (CauchyCompletionSplitUp.mk
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist X))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist U))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist V))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist A))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist I))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist G))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist W))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist D))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist R))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist E))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist H))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist C))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist P))
            (cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist N))) =
          some (CauchyCompletionSplitUp.mk X U V A I G W D R E H C P N)
      rw [cauchyCompletionSplitDecodeEncodeBHist X,
        cauchyCompletionSplitDecodeEncodeBHist U,
        cauchyCompletionSplitDecodeEncodeBHist V,
        cauchyCompletionSplitDecodeEncodeBHist A,
        cauchyCompletionSplitDecodeEncodeBHist I,
        cauchyCompletionSplitDecodeEncodeBHist G,
        cauchyCompletionSplitDecodeEncodeBHist W,
        cauchyCompletionSplitDecodeEncodeBHist D,
        cauchyCompletionSplitDecodeEncodeBHist R,
        cauchyCompletionSplitDecodeEncodeBHist E,
        cauchyCompletionSplitDecodeEncodeBHist H,
        cauchyCompletionSplitDecodeEncodeBHist C,
        cauchyCompletionSplitDecodeEncodeBHist P,
        cauchyCompletionSplitDecodeEncodeBHist N]

private theorem cauchyCompletionSplitToEventFlow_injective
    {x y : CauchyCompletionSplitUp} :
    cauchyCompletionSplitToEventFlow x = cauchyCompletionSplitToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionSplitFromEventFlow (cauchyCompletionSplitToEventFlow x) =
        cauchyCompletionSplitFromEventFlow (cauchyCompletionSplitToEventFlow y) :=
    congrArg cauchyCompletionSplitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionSplitRoundTrip x).symm
      (Eq.trans hread (cauchyCompletionSplitRoundTrip y)))

private theorem cauchyCompletionSplitFieldsFaithful :
    forall x y : CauchyCompletionSplitUp,
      cauchyCompletionSplitFields x = cauchyCompletionSplitFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 U1 V1 A1 I1 G1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 U2 V2 A2 I2 G2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletionSplitBHistCarrier :
    BHistCarrier CauchyCompletionSplitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionSplitToEventFlow
  fromEventFlow := cauchyCompletionSplitFromEventFlow

instance cauchyCompletionSplitChapterTasteGate :
    ChapterTasteGate CauchyCompletionSplitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionSplitFromEventFlow (cauchyCompletionSplitToEventFlow x) = some x
    exact cauchyCompletionSplitRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionSplitToEventFlow_injective heq)

instance cauchyCompletionSplitFieldFaithful :
    FieldFaithful CauchyCompletionSplitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionSplitFields
  field_faithful := cauchyCompletionSplitFieldsFaithful

instance cauchyCompletionSplitNontrivial : Nontrivial CauchyCompletionSplitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionSplitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionSplitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionSplitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionSplitChapterTasteGate

theorem CauchyCompletionSplitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionSplitUp) /\
      Nonempty (FieldFaithful CauchyCompletionSplitUp) /\
        Nonempty (Nontrivial CauchyCompletionSplitUp) /\
          (forall h : BHist,
            cauchyCompletionSplitDecodeBHist (cauchyCompletionSplitEncodeBHist h) = h) /\
            (forall x : CauchyCompletionSplitUp,
              cauchyCompletionSplitFromEventFlow (cauchyCompletionSplitToEventFlow x) =
                some x) /\
              cauchyCompletionSplitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨⟨cauchyCompletionSplitChapterTasteGate⟩,
      ⟨⟨cauchyCompletionSplitFieldFaithful⟩,
        ⟨⟨cauchyCompletionSplitNontrivial⟩,
          cauchyCompletionSplitDecodeEncodeBHist,
          cauchyCompletionSplitRoundTrip,
          rfl⟩⟩⟩

end BEDC.Derived.CauchyCompletionSplitUp
