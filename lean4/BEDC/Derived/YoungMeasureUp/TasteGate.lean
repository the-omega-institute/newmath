import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YoungMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YoungMeasureUp : Type where
  | mk (R P T S Q E H C K N : BHist) : YoungMeasureUp
  deriving DecidableEq

def youngMeasureFields : YoungMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YoungMeasureUp.mk R P T S Q E H C K N => [R, P, T, S, Q, E, H, C, K, N]

def youngMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: youngMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: youngMeasureEncodeBHist h

def youngMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (youngMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (youngMeasureDecodeBHist tail)

private theorem youngMeasure_decode_encode :
    ∀ h : BHist, youngMeasureDecodeBHist (youngMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def youngMeasureToEventFlow : YoungMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map youngMeasureEncodeBHist (youngMeasureFields x)

private def youngMeasureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => youngMeasureEventAtDefault index rest

def youngMeasureFromEventFlow (ef : EventFlow) : Option YoungMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (YoungMeasureUp.mk
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 0 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 1 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 2 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 3 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 4 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 5 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 6 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 7 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 8 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 9 ef)))

private theorem youngMeasure_round_trip :
    ∀ x : YoungMeasureUp,
      youngMeasureFromEventFlow (youngMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R P T S Q E H C K N =>
      change
        some
          (YoungMeasureUp.mk
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist R))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist P))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist T))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist S))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist Q))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist E))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist H))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist C))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist K))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist N))) =
          some (YoungMeasureUp.mk R P T S Q E H C K N)
      rw [youngMeasure_decode_encode R,
        youngMeasure_decode_encode P,
        youngMeasure_decode_encode T,
        youngMeasure_decode_encode S,
        youngMeasure_decode_encode Q,
        youngMeasure_decode_encode E,
        youngMeasure_decode_encode H,
        youngMeasure_decode_encode C,
        youngMeasure_decode_encode K,
        youngMeasure_decode_encode N]

private theorem youngMeasureToEventFlow_injective {x y : YoungMeasureUp} :
    youngMeasureToEventFlow x = youngMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      youngMeasureFromEventFlow (youngMeasureToEventFlow x) =
        youngMeasureFromEventFlow (youngMeasureToEventFlow y) :=
    congrArg youngMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (youngMeasure_round_trip x).symm
      (Eq.trans hread (youngMeasure_round_trip y)))

instance youngMeasureBHistCarrier : BHistCarrier YoungMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := youngMeasureToEventFlow
  fromEventFlow := youngMeasureFromEventFlow

instance youngMeasureChapterTasteGate : ChapterTasteGate YoungMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change youngMeasureFromEventFlow (youngMeasureToEventFlow x) = some x
    exact youngMeasure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (youngMeasureToEventFlow_injective heq)

theorem YoungMeasureCarrier_namecert_obligations (x : YoungMeasureUp) :
    ∃ localCert : BHist,
      SemanticNameCert
        (fun row : BHist => hsame row localCert ∧ localCert ∈ youngMeasureFields x)
        (fun row : BHist => hsame row localCert ∧ localCert ∈ youngMeasureFields x)
        (fun row : BHist => hsame row localCert ∧ localCert ∈ youngMeasureFields x)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk R P T S Q E H C K localCert =>
      refine ⟨localCert, ?_⟩
      refine
        { core :=
            { carrier_inhabited := ?_
              equiv_refl := ?_
              equiv_symm := ?_
              equiv_trans := ?_
              carrier_respects_equiv := ?_ }
          pattern_sound := ?_
          ledger_sound := ?_ }
      · exact
          ⟨localCert, hsame_refl localCert,
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <|
                        List.Mem.tail _ <|
                          List.Mem.tail _ <|
                            List.Mem.tail _ <| List.Mem.head _⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' same₁ same₂
        exact hsame_trans same₁ same₂
      · intro _row _row' same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      · intro _row source
        exact source
      · intro _row source
        exact source

end BEDC.Derived.YoungMeasureUp
