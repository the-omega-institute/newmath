import BEDC.Derived.DyadicValuationUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicValuationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def dyadicValuationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicValuationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicValuationEncodeBHist h

def dyadicValuationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicValuationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicValuationDecodeBHist tail)

private theorem dyadicValuationDecode_encode :
    ∀ h : BHist, dyadicValuationDecodeBHist (dyadicValuationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicValuationToEventFlow : BEDC.Derived.DyadicValuationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => BEDC.Derived.dyadicValuationFields x |>.map dyadicValuationEncodeBHist

def dyadicValuationFromEventFlow : EventFlow → Option BEDC.Derived.DyadicValuationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: restE =>
      match restE with
      | [] => none
      | E :: restZ =>
          match restZ with
          | [] => none
          | Z :: restV =>
              match restV with
              | [] => none
              | V :: restC =>
                  match restC with
                  | [] => none
                  | C :: restT =>
                      match restT with
                      | [] => none
                      | T :: restH =>
                          match restH with
                          | [] => none
                          | H :: restR =>
                              match restR with
                              | [] => none
                              | R :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (BEDC.Derived.DyadicValuationUp.mk
                                                  (dyadicValuationDecodeBHist M)
                                                  (dyadicValuationDecodeBHist E)
                                                  (dyadicValuationDecodeBHist Z)
                                                  (dyadicValuationDecodeBHist V)
                                                  (dyadicValuationDecodeBHist C)
                                                  (dyadicValuationDecodeBHist T)
                                                  (dyadicValuationDecodeBHist H)
                                                  (dyadicValuationDecodeBHist R)
                                                  (dyadicValuationDecodeBHist P)
                                                  (dyadicValuationDecodeBHist N))
                                          | _ :: _ => none

private theorem dyadicValuation_round_trip :
    ∀ x : BEDC.Derived.DyadicValuationUp,
      dyadicValuationFromEventFlow (dyadicValuationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E Z V C T H R P N =>
      change
        some
          (BEDC.Derived.DyadicValuationUp.mk
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist M))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist E))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist Z))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist V))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist C))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist T))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist H))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist R))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist P))
            (dyadicValuationDecodeBHist (dyadicValuationEncodeBHist N))) =
          some (BEDC.Derived.DyadicValuationUp.mk M E Z V C T H R P N)
      rw [dyadicValuationDecode_encode M, dyadicValuationDecode_encode E,
        dyadicValuationDecode_encode Z, dyadicValuationDecode_encode V,
        dyadicValuationDecode_encode C, dyadicValuationDecode_encode T,
        dyadicValuationDecode_encode H, dyadicValuationDecode_encode R,
        dyadicValuationDecode_encode P, dyadicValuationDecode_encode N]

private theorem dyadicValuationToEventFlow_injective
    {x y : BEDC.Derived.DyadicValuationUp} :
    dyadicValuationToEventFlow x = dyadicValuationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicValuationFromEventFlow (dyadicValuationToEventFlow x) =
        dyadicValuationFromEventFlow (dyadicValuationToEventFlow y) :=
    congrArg dyadicValuationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicValuation_round_trip x).symm
      (Eq.trans hread (dyadicValuation_round_trip y)))

instance dyadicValuationBHistCarrier : BHistCarrier BEDC.Derived.DyadicValuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicValuationToEventFlow
  fromEventFlow := dyadicValuationFromEventFlow

instance dyadicValuationChapterTasteGate :
    ChapterTasteGate BEDC.Derived.DyadicValuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicValuationFromEventFlow (dyadicValuationToEventFlow x) = some x
    exact dyadicValuation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicValuationToEventFlow_injective heq)

theorem DyadicValuationTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicValuationDecodeBHist (dyadicValuationEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.DyadicValuationUp,
        dyadicValuationFromEventFlow (dyadicValuationToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.DyadicValuationUp,
          dyadicValuationToEventFlow x = dyadicValuationToEventFlow y → x = y) ∧
          dyadicValuationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact dyadicValuationDecode_encode
  constructor
  · exact dyadicValuation_round_trip
  constructor
  · intro x y heq
    exact dyadicValuationToEventFlow_injective heq
  · rfl

end BEDC.Derived.DyadicValuationUp
