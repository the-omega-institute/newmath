import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniFiniteMinimumBudgetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniFiniteMinimumBudgetUp : Type where
  | mk (K F D U Q E H C P N : BHist) : DiniFiniteMinimumBudgetUp

def diniFiniteMinimumBudgetEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniFiniteMinimumBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniFiniteMinimumBudgetEncodeBHist h

def diniFiniteMinimumBudgetDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniFiniteMinimumBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniFiniteMinimumBudgetDecodeBHist tail)

private theorem diniFiniteMinimumBudgetDecode_encode :
    forall h : BHist,
      diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem diniFiniteMinimumBudgetEncode_injective {h k : BHist} :
    diniFiniteMinimumBudgetEncodeBHist h = diniFiniteMinimumBudgetEncodeBHist k -> h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have decoded :
      diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist h) =
        diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist k) :=
    congrArg diniFiniteMinimumBudgetDecodeBHist heq
  rw [diniFiniteMinimumBudgetDecode_encode h, diniFiniteMinimumBudgetDecode_encode k] at decoded
  exact decoded

def diniFiniteMinimumBudgetFields : DiniFiniteMinimumBudgetUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniFiniteMinimumBudgetUp.mk K F D U Q E H C P N => [K, F, D, U, Q, E, H, C, P, N]

def diniFiniteMinimumBudgetToEventFlow : DiniFiniteMinimumBudgetUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => diniFiniteMinimumBudgetFields x |>.map diniFiniteMinimumBudgetEncodeBHist

private def diniFiniteMinimumBudgetEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diniFiniteMinimumBudgetEventAtDefault index rest

def diniFiniteMinimumBudgetFromEventFlow
    (ef : EventFlow) : Option DiniFiniteMinimumBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiniFiniteMinimumBudgetUp.mk
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 0 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 1 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 2 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 3 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 4 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 5 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 6 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 7 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 8 ef))
      (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEventAtDefault 9 ef)))

private theorem diniFiniteMinimumBudget_round_trip (x : DiniFiniteMinimumBudgetUp) :
    diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F D U Q E H C P N =>
      change
        some
          (DiniFiniteMinimumBudgetUp.mk
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist K))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist F))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist D))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist U))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist Q))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist E))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist H))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist C))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist P))
            (diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist N))) =
          some (DiniFiniteMinimumBudgetUp.mk K F D U Q E H C P N)
      rw [diniFiniteMinimumBudgetDecode_encode K, diniFiniteMinimumBudgetDecode_encode F,
        diniFiniteMinimumBudgetDecode_encode D, diniFiniteMinimumBudgetDecode_encode U,
        diniFiniteMinimumBudgetDecode_encode Q, diniFiniteMinimumBudgetDecode_encode E,
        diniFiniteMinimumBudgetDecode_encode H, diniFiniteMinimumBudgetDecode_encode C,
        diniFiniteMinimumBudgetDecode_encode P, diniFiniteMinimumBudgetDecode_encode N]

private theorem diniFiniteMinimumBudgetToEventFlow_injective
    {x y : DiniFiniteMinimumBudgetUp} :
    diniFiniteMinimumBudgetToEventFlow x = diniFiniteMinimumBudgetToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) =
        diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow y) :=
    congrArg diniFiniteMinimumBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diniFiniteMinimumBudget_round_trip x).symm
      (Eq.trans hread (diniFiniteMinimumBudget_round_trip y)))

instance diniFiniteMinimumBudgetBHistCarrier : BHistCarrier DiniFiniteMinimumBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniFiniteMinimumBudgetToEventFlow
  fromEventFlow := diniFiniteMinimumBudgetFromEventFlow

instance diniFiniteMinimumBudgetChapterTasteGate :
    ChapterTasteGate DiniFiniteMinimumBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) = some x
    exact diniFiniteMinimumBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diniFiniteMinimumBudgetToEventFlow_injective heq)

theorem DiniFiniteMinimumBudgetTasteGate_single_carrier_alignment :
    (forall h : BHist,
      diniFiniteMinimumBudgetDecodeBHist (diniFiniteMinimumBudgetEncodeBHist h) = h) ∧
      (forall x : DiniFiniteMinimumBudgetUp,
        diniFiniteMinimumBudgetFromEventFlow (diniFiniteMinimumBudgetToEventFlow x) =
          some x) ∧
      (forall x y : DiniFiniteMinimumBudgetUp,
        diniFiniteMinimumBudgetToEventFlow x = diniFiniteMinimumBudgetToEventFlow y ->
          x = y) ∧
      diniFiniteMinimumBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diniFiniteMinimumBudgetDecode_encode
  · constructor
    · exact diniFiniteMinimumBudget_round_trip
    · constructor
      · intro x y heq
        cases x with
        | mk sourceK sourceF sourceD sourceU sourceQ sourceE sourceH sourceC sourceP sourceN =>
            cases y with
            | mk targetK targetF targetD targetU targetQ targetE targetH targetC targetP
                targetN =>
                change
                  [diniFiniteMinimumBudgetEncodeBHist sourceK,
                    diniFiniteMinimumBudgetEncodeBHist sourceF,
                    diniFiniteMinimumBudgetEncodeBHist sourceD,
                    diniFiniteMinimumBudgetEncodeBHist sourceU,
                    diniFiniteMinimumBudgetEncodeBHist sourceQ,
                    diniFiniteMinimumBudgetEncodeBHist sourceE,
                    diniFiniteMinimumBudgetEncodeBHist sourceH,
                    diniFiniteMinimumBudgetEncodeBHist sourceC,
                    diniFiniteMinimumBudgetEncodeBHist sourceP,
                    diniFiniteMinimumBudgetEncodeBHist sourceN] =
                  [diniFiniteMinimumBudgetEncodeBHist targetK,
                    diniFiniteMinimumBudgetEncodeBHist targetF,
                    diniFiniteMinimumBudgetEncodeBHist targetD,
                    diniFiniteMinimumBudgetEncodeBHist targetU,
                    diniFiniteMinimumBudgetEncodeBHist targetQ,
                    diniFiniteMinimumBudgetEncodeBHist targetE,
                    diniFiniteMinimumBudgetEncodeBHist targetH,
                    diniFiniteMinimumBudgetEncodeBHist targetC,
                    diniFiniteMinimumBudgetEncodeBHist targetP,
                    diniFiniteMinimumBudgetEncodeBHist targetN] at heq
                injection heq with hK rest1
                injection rest1 with hF rest2
                injection rest2 with hD rest3
                injection rest3 with hU rest4
                injection rest4 with hQ rest5
                injection rest5 with hE rest6
                injection rest6 with hH rest7
                injection rest7 with hC rest8
                injection rest8 with hP rest9
                injection rest9 with hN _
                cases diniFiniteMinimumBudgetEncode_injective hK
                cases diniFiniteMinimumBudgetEncode_injective hF
                cases diniFiniteMinimumBudgetEncode_injective hD
                cases diniFiniteMinimumBudgetEncode_injective hU
                cases diniFiniteMinimumBudgetEncode_injective hQ
                cases diniFiniteMinimumBudgetEncode_injective hE
                cases diniFiniteMinimumBudgetEncode_injective hH
                cases diniFiniteMinimumBudgetEncode_injective hC
                cases diniFiniteMinimumBudgetEncode_injective hP
                cases diniFiniteMinimumBudgetEncode_injective hN
                rfl
      · rfl

end BEDC.Derived.DiniFiniteMinimumBudgetUp.TasteGate
