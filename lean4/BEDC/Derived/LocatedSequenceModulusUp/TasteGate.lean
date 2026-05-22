import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSequenceModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSequenceModulusUp : Type where
  | mk : (L M D S R E H C P N : BHist) → LocatedSequenceModulusUp
  deriving DecidableEq

def locatedSequenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSequenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSequenceModulusEncodeBHist h

def locatedSequenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSequenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSequenceModulusDecodeBHist tail)

private theorem locatedSequenceModulusDecodeEncodeBHist :
    ∀ h : BHist,
      locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedSequenceModulusFields : LocatedSequenceModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSequenceModulusUp.mk L M D S R E H C P N => [L, M, D, S, R, E, H, C, P, N]

def locatedSequenceModulusToEventFlow : LocatedSequenceModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedSequenceModulusFields x).map locatedSequenceModulusEncodeBHist

def locatedSequenceModulusFromEventFlow : EventFlow → Option LocatedSequenceModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restL =>
      match restL with
      | [] => none
      | M :: restM =>
          match restM with
          | [] => none
          | D :: restD =>
              match restD with
              | [] => none
              | S :: restS =>
                  match restS with
                  | [] => none
                  | R :: restR =>
                      match restR with
                      | [] => none
                      | E :: restE =>
                          match restE with
                          | [] => none
                          | H :: restH =>
                              match restH with
                              | [] => none
                              | C :: restC =>
                                  match restC with
                                  | [] => none
                                  | P :: restP =>
                                      match restP with
                                      | [] => none
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (LocatedSequenceModulusUp.mk
                                                  (locatedSequenceModulusDecodeBHist L)
                                                  (locatedSequenceModulusDecodeBHist M)
                                                  (locatedSequenceModulusDecodeBHist D)
                                                  (locatedSequenceModulusDecodeBHist S)
                                                  (locatedSequenceModulusDecodeBHist R)
                                                  (locatedSequenceModulusDecodeBHist E)
                                                  (locatedSequenceModulusDecodeBHist H)
                                                  (locatedSequenceModulusDecodeBHist C)
                                                  (locatedSequenceModulusDecodeBHist P)
                                                  (locatedSequenceModulusDecodeBHist N))
                                          | _ :: _ => none

private theorem locatedSequenceModulus_round_trip :
    ∀ x : LocatedSequenceModulusUp,
      locatedSequenceModulusFromEventFlow (locatedSequenceModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L M D S R E H C P N =>
      change
        some
          (LocatedSequenceModulusUp.mk
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist L))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist M))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist D))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist S))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist R))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist E))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist H))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist C))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist P))
            (locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist N))) =
          some (LocatedSequenceModulusUp.mk L M D S R E H C P N)
      rw [locatedSequenceModulusDecodeEncodeBHist L,
        locatedSequenceModulusDecodeEncodeBHist M,
        locatedSequenceModulusDecodeEncodeBHist D,
        locatedSequenceModulusDecodeEncodeBHist S,
        locatedSequenceModulusDecodeEncodeBHist R,
        locatedSequenceModulusDecodeEncodeBHist E,
        locatedSequenceModulusDecodeEncodeBHist H,
        locatedSequenceModulusDecodeEncodeBHist C,
        locatedSequenceModulusDecodeEncodeBHist P,
        locatedSequenceModulusDecodeEncodeBHist N]

private theorem locatedSequenceModulusToEventFlow_injective
    {x y : LocatedSequenceModulusUp} :
    locatedSequenceModulusToEventFlow x = locatedSequenceModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedSequenceModulusFromEventFlow (locatedSequenceModulusToEventFlow x) =
        locatedSequenceModulusFromEventFlow (locatedSequenceModulusToEventFlow y) :=
    congrArg locatedSequenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedSequenceModulus_round_trip x).symm
      (Eq.trans hread (locatedSequenceModulus_round_trip y)))

instance locatedSequenceModulusBHistCarrier : BHistCarrier LocatedSequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSequenceModulusToEventFlow
  fromEventFlow := locatedSequenceModulusFromEventFlow

instance locatedSequenceModulusChapterTasteGate :
    ChapterTasteGate LocatedSequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedSequenceModulusFromEventFlow (locatedSequenceModulusToEventFlow x) = some x
    exact locatedSequenceModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedSequenceModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedSequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedSequenceModulusChapterTasteGate

theorem LocatedSequenceModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedSequenceModulusDecodeBHist (locatedSequenceModulusEncodeBHist h) = h) ∧
      (∀ x : LocatedSequenceModulusUp,
        locatedSequenceModulusFromEventFlow (locatedSequenceModulusToEventFlow x) = some x) ∧
        (∀ x y : LocatedSequenceModulusUp,
          locatedSequenceModulusToEventFlow x = locatedSequenceModulusToEventFlow y → x = y) ∧
          locatedSequenceModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨locatedSequenceModulusDecodeEncodeBHist,
      locatedSequenceModulus_round_trip,
      (fun _ _ heq => locatedSequenceModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedSequenceModulusUp
