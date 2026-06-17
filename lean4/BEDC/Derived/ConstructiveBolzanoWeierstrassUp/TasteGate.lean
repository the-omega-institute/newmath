import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveBolzanoWeierstrassUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveBolzanoWeierstrassUp : Type where
  | mk (S B I T R Q E H C P N : BHist) : ConstructiveBolzanoWeierstrassUp

def constructiveBolzanoWeierstrassEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveBolzanoWeierstrassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveBolzanoWeierstrassEncodeBHist h

def constructiveBolzanoWeierstrassDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveBolzanoWeierstrassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveBolzanoWeierstrassDecodeBHist tail)

private theorem constructiveBolzanoWeierstrassDecode_encode :
    forall h : BHist,
      constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem constructiveBolzanoWeierstrassEncode_injective {h k : BHist} :
    constructiveBolzanoWeierstrassEncodeBHist h =
      constructiveBolzanoWeierstrassEncodeBHist k -> h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have decoded :
      constructiveBolzanoWeierstrassDecodeBHist
          (constructiveBolzanoWeierstrassEncodeBHist h) =
        constructiveBolzanoWeierstrassDecodeBHist
          (constructiveBolzanoWeierstrassEncodeBHist k) :=
    congrArg constructiveBolzanoWeierstrassDecodeBHist heq
  rw [constructiveBolzanoWeierstrassDecode_encode h,
    constructiveBolzanoWeierstrassDecode_encode k] at decoded
  exact decoded

def constructiveBolzanoWeierstrassFields :
    ConstructiveBolzanoWeierstrassUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveBolzanoWeierstrassUp.mk S B I T R Q E H C P N =>
      [S, B, I, T, R, Q, E, H, C, P, N]

def constructiveBolzanoWeierstrassToEventFlow :
    ConstructiveBolzanoWeierstrassUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => constructiveBolzanoWeierstrassFields x |>.map constructiveBolzanoWeierstrassEncodeBHist

private def constructiveBolzanoWeierstrassEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveBolzanoWeierstrassEventAtDefault index rest

def constructiveBolzanoWeierstrassFromEventFlow
    (ef : EventFlow) : Option ConstructiveBolzanoWeierstrassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveBolzanoWeierstrassUp.mk
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 0 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 1 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 2 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 3 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 4 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 5 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 6 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 7 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 8 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 9 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 10 ef)))

private theorem constructiveBolzanoWeierstrass_round_trip
    (x : ConstructiveBolzanoWeierstrassUp) :
    constructiveBolzanoWeierstrassFromEventFlow
      (constructiveBolzanoWeierstrassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S B I T R Q E H C P N =>
      change
        some
          (ConstructiveBolzanoWeierstrassUp.mk
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist S))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist B))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist I))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist T))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist R))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist Q))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist E))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist H))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist C))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist P))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist N))) =
          some (ConstructiveBolzanoWeierstrassUp.mk S B I T R Q E H C P N)
      rw [constructiveBolzanoWeierstrassDecode_encode S,
        constructiveBolzanoWeierstrassDecode_encode B,
        constructiveBolzanoWeierstrassDecode_encode I,
        constructiveBolzanoWeierstrassDecode_encode T,
        constructiveBolzanoWeierstrassDecode_encode R,
        constructiveBolzanoWeierstrassDecode_encode Q,
        constructiveBolzanoWeierstrassDecode_encode E,
        constructiveBolzanoWeierstrassDecode_encode H,
        constructiveBolzanoWeierstrassDecode_encode C,
        constructiveBolzanoWeierstrassDecode_encode P,
        constructiveBolzanoWeierstrassDecode_encode N]

private theorem constructiveBolzanoWeierstrassToEventFlow_injective
    {x y : ConstructiveBolzanoWeierstrassUp} :
    constructiveBolzanoWeierstrassToEventFlow x =
        constructiveBolzanoWeierstrassToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveBolzanoWeierstrassFromEventFlow
          (constructiveBolzanoWeierstrassToEventFlow x) =
        constructiveBolzanoWeierstrassFromEventFlow
          (constructiveBolzanoWeierstrassToEventFlow y) :=
    congrArg constructiveBolzanoWeierstrassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (constructiveBolzanoWeierstrass_round_trip x).symm
      (Eq.trans hread (constructiveBolzanoWeierstrass_round_trip y)))

instance constructiveBolzanoWeierstrassBHistCarrier :
    BHistCarrier ConstructiveBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveBolzanoWeierstrassToEventFlow
  fromEventFlow := constructiveBolzanoWeierstrassFromEventFlow

instance constructiveBolzanoWeierstrassChapterTasteGate :
    ChapterTasteGate ConstructiveBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveBolzanoWeierstrassFromEventFlow
        (constructiveBolzanoWeierstrassToEventFlow x) = some x
    exact constructiveBolzanoWeierstrass_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveBolzanoWeierstrassToEventFlow_injective heq)

theorem ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment :
    (forall h : BHist,
      constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEncodeBHist h) = h) ∧
      (forall x : ConstructiveBolzanoWeierstrassUp,
        constructiveBolzanoWeierstrassFromEventFlow
          (constructiveBolzanoWeierstrassToEventFlow x) = some x) ∧
      (forall x y : ConstructiveBolzanoWeierstrassUp,
        constructiveBolzanoWeierstrassToEventFlow x =
          constructiveBolzanoWeierstrassToEventFlow y -> x = y) ∧
      constructiveBolzanoWeierstrassEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact constructiveBolzanoWeierstrassDecode_encode
  · constructor
    · exact constructiveBolzanoWeierstrass_round_trip
    · constructor
      · intro x y heq
        cases x with
        | mk sourceS sourceB sourceI sourceT sourceR sourceQ sourceE sourceH sourceC
            sourceP sourceN =>
            cases y with
            | mk targetS targetB targetI targetT targetR targetQ targetE targetH targetC
                targetP targetN =>
                change
                  [constructiveBolzanoWeierstrassEncodeBHist sourceS,
                    constructiveBolzanoWeierstrassEncodeBHist sourceB,
                    constructiveBolzanoWeierstrassEncodeBHist sourceI,
                    constructiveBolzanoWeierstrassEncodeBHist sourceT,
                    constructiveBolzanoWeierstrassEncodeBHist sourceR,
                    constructiveBolzanoWeierstrassEncodeBHist sourceQ,
                    constructiveBolzanoWeierstrassEncodeBHist sourceE,
                    constructiveBolzanoWeierstrassEncodeBHist sourceH,
                    constructiveBolzanoWeierstrassEncodeBHist sourceC,
                    constructiveBolzanoWeierstrassEncodeBHist sourceP,
                    constructiveBolzanoWeierstrassEncodeBHist sourceN] =
                  [constructiveBolzanoWeierstrassEncodeBHist targetS,
                    constructiveBolzanoWeierstrassEncodeBHist targetB,
                    constructiveBolzanoWeierstrassEncodeBHist targetI,
                    constructiveBolzanoWeierstrassEncodeBHist targetT,
                    constructiveBolzanoWeierstrassEncodeBHist targetR,
                    constructiveBolzanoWeierstrassEncodeBHist targetQ,
                    constructiveBolzanoWeierstrassEncodeBHist targetE,
                    constructiveBolzanoWeierstrassEncodeBHist targetH,
                    constructiveBolzanoWeierstrassEncodeBHist targetC,
                    constructiveBolzanoWeierstrassEncodeBHist targetP,
                    constructiveBolzanoWeierstrassEncodeBHist targetN] at heq
                injection heq with hS rest1
                injection rest1 with hB rest2
                injection rest2 with hI rest3
                injection rest3 with hT rest4
                injection rest4 with hR rest5
                injection rest5 with hQ rest6
                injection rest6 with hE rest7
                injection rest7 with hH rest8
                injection rest8 with hC rest9
                injection rest9 with hP rest10
                injection rest10 with hN _
                cases constructiveBolzanoWeierstrassEncode_injective hS
                cases constructiveBolzanoWeierstrassEncode_injective hB
                cases constructiveBolzanoWeierstrassEncode_injective hI
                cases constructiveBolzanoWeierstrassEncode_injective hT
                cases constructiveBolzanoWeierstrassEncode_injective hR
                cases constructiveBolzanoWeierstrassEncode_injective hQ
                cases constructiveBolzanoWeierstrassEncode_injective hE
                cases constructiveBolzanoWeierstrassEncode_injective hH
                cases constructiveBolzanoWeierstrassEncode_injective hC
                cases constructiveBolzanoWeierstrassEncode_injective hP
                cases constructiveBolzanoWeierstrassEncode_injective hN
                rfl
      · rfl

end BEDC.Derived.ConstructiveBolzanoWeierstrassUp.TasteGate
