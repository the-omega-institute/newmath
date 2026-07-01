import BEDC.Derived.TaylorRemainderUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TaylorRemainderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def taylorRemainderEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: taylorRemainderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: taylorRemainderEncodeBHist h

def taylorRemainderDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (taylorRemainderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (taylorRemainderDecodeBHist tail)

private theorem taylorRemainderDecode_encode_bhist :
    forall h : BHist, taylorRemainderDecodeBHist (taylorRemainderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def taylorRemainderToEventFlow : TaylorRemainderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TaylorRemainderUp.mk D P W E Q S H C G N =>
      [[BMark.b0],
        taylorRemainderEncodeBHist D,
        [BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        taylorRemainderEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        taylorRemainderEncodeBHist N]

private def taylorRemainderEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => taylorRemainderEventAtDefault index rest

def taylorRemainderFromEventFlow (ef : EventFlow) : Option TaylorRemainderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TaylorRemainderUp.mk
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 1 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 3 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 5 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 7 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 9 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 11 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 13 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 15 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 17 ef))
      (taylorRemainderDecodeBHist (taylorRemainderEventAtDefault 19 ef)))

private theorem taylorRemainder_round_trip :
    forall x : TaylorRemainderUp,
      taylorRemainderFromEventFlow (taylorRemainderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D P W E Q S H C G N =>
      change
        some
          (TaylorRemainderUp.mk
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist D))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist P))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist W))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist E))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist Q))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist S))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist H))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist C))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist G))
            (taylorRemainderDecodeBHist (taylorRemainderEncodeBHist N))) =
          some (TaylorRemainderUp.mk D P W E Q S H C G N)
      rw [taylorRemainderDecode_encode_bhist D,
        taylorRemainderDecode_encode_bhist P,
        taylorRemainderDecode_encode_bhist W,
        taylorRemainderDecode_encode_bhist E,
        taylorRemainderDecode_encode_bhist Q,
        taylorRemainderDecode_encode_bhist S,
        taylorRemainderDecode_encode_bhist H,
        taylorRemainderDecode_encode_bhist C,
        taylorRemainderDecode_encode_bhist G,
        taylorRemainderDecode_encode_bhist N]

private theorem taylorRemainderToEventFlow_injective {x y : TaylorRemainderUp} :
    taylorRemainderToEventFlow x = taylorRemainderToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      taylorRemainderFromEventFlow (taylorRemainderToEventFlow x) =
        taylorRemainderFromEventFlow (taylorRemainderToEventFlow y) :=
    congrArg taylorRemainderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (taylorRemainder_round_trip x).symm
      (Eq.trans hread (taylorRemainder_round_trip y)))

instance taylorRemainderBHistCarrier : BHistCarrier TaylorRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := taylorRemainderToEventFlow
  fromEventFlow := taylorRemainderFromEventFlow

instance taylorRemainderChapterTasteGate : ChapterTasteGate TaylorRemainderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change taylorRemainderFromEventFlow (taylorRemainderToEventFlow x) = some x
    exact taylorRemainder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (taylorRemainderToEventFlow_injective heq)

theorem TaylorRemainderCarrier_namecert_obligations (x : TaylorRemainderUp) :
    exists D P W E Q S H C G N : BHist,
      x = TaylorRemainderUp.mk D P W E Q S H C G N ∧
        hsame H H ∧ hsame C C ∧ hsame G G ∧ hsame N N ∧
          taylorRemainderEncodeBHist BHist.Empty = ([] : List BMark) ∧
            List.Mem (taylorRemainderEncodeBHist D) (BHistCarrier.toEventFlow x) := by
  -- BEDC touchpoint anchor: BHist BMark hsame BHistCarrier
  cases x with
  | mk D P W E Q S H C G N =>
      refine
        ⟨D, P, W, E, Q, S, H, C, G, N, rfl, hsame_refl H, hsame_refl C,
          hsame_refl G, hsame_refl N, rfl, ?_⟩
      simp only [BHistCarrier.toEventFlow, taylorRemainderToEventFlow]
      exact List.Mem.tail _ (List.Mem.head _)

end BEDC.Derived.TaylorRemainderUp
