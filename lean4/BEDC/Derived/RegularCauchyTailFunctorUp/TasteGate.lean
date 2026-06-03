import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailFunctorUp : Type where
  | mk (R C T F M S E H P N L : BHist) : RegularCauchyTailFunctorUp
  deriving DecidableEq

def regularCauchyTailFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailFunctorEncodeBHist h

def regularCauchyTailFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailFunctorDecodeBHist tail)

private theorem RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyTailFunctorDecodeBHist
          (regularCauchyTailFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailFunctorToEventFlow : RegularCauchyTailFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailFunctorUp.mk R C T F M S E H P N L =>
      [regularCauchyTailFunctorEncodeBHist R,
        regularCauchyTailFunctorEncodeBHist C,
        regularCauchyTailFunctorEncodeBHist T,
        regularCauchyTailFunctorEncodeBHist F,
        regularCauchyTailFunctorEncodeBHist M,
        regularCauchyTailFunctorEncodeBHist S,
        regularCauchyTailFunctorEncodeBHist E,
        regularCauchyTailFunctorEncodeBHist H,
        regularCauchyTailFunctorEncodeBHist P,
        regularCauchyTailFunctorEncodeBHist N,
        regularCauchyTailFunctorEncodeBHist L]

def regularCauchyTailFunctorFromEventFlow : EventFlow → Option RegularCauchyTailFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: restC =>
      match restC with
      | [] => none
      | C :: restT =>
          match restT with
          | [] => none
          | T :: restF =>
              match restF with
              | [] => none
              | F :: restM =>
                  match restM with
                  | [] => none
                  | M :: restS =>
                      match restS with
                      | [] => none
                      | S :: restE =>
                          match restE with
                          | [] => none
                          | E :: restH =>
                              match restH with
                              | [] => none
                              | H :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: restL =>
                                          match restL with
                                          | [] => none
                                          | L :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (RegularCauchyTailFunctorUp.mk
                                                      (regularCauchyTailFunctorDecodeBHist R)
                                                      (regularCauchyTailFunctorDecodeBHist C)
                                                      (regularCauchyTailFunctorDecodeBHist T)
                                                      (regularCauchyTailFunctorDecodeBHist F)
                                                      (regularCauchyTailFunctorDecodeBHist M)
                                                      (regularCauchyTailFunctorDecodeBHist S)
                                                      (regularCauchyTailFunctorDecodeBHist E)
                                                      (regularCauchyTailFunctorDecodeBHist H)
                                                      (regularCauchyTailFunctorDecodeBHist P)
                                                      (regularCauchyTailFunctorDecodeBHist N)
                                                      (regularCauchyTailFunctorDecodeBHist L))
                                              | _ :: _ => none

private theorem RegularCauchyTailFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyTailFunctorUp,
      regularCauchyTailFunctorFromEventFlow
          (regularCauchyTailFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R C T F M S E H P N L =>
      change
        some
          (RegularCauchyTailFunctorUp.mk
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist R))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist C))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist T))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist F))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist M))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist S))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist E))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist H))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist P))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist N))
            (regularCauchyTailFunctorDecodeBHist (regularCauchyTailFunctorEncodeBHist L))) =
          some (RegularCauchyTailFunctorUp.mk R C T F M S E H P N L)
      rw [RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode R,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode C,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode T,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode F,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode M,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode S,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode E,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode H,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode P,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode N,
        RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode L]

private theorem RegularCauchyTailFunctorToEventFlow_injective
    {x y : RegularCauchyTailFunctorUp} :
    regularCauchyTailFunctorToEventFlow x =
        regularCauchyTailFunctorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailFunctorFromEventFlow (regularCauchyTailFunctorToEventFlow x) =
        regularCauchyTailFunctorFromEventFlow (regularCauchyTailFunctorToEventFlow y) :=
    congrArg regularCauchyTailFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyTailFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTailFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyTailFunctorBHistCarrier :
    BHistCarrier RegularCauchyTailFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailFunctorToEventFlow
  fromEventFlow := regularCauchyTailFunctorFromEventFlow

instance regularCauchyTailFunctorChapterTasteGate :
    ChapterTasteGate RegularCauchyTailFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailFunctorFromEventFlow
          (regularCauchyTailFunctorToEventFlow x) = some x
    exact RegularCauchyTailFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyTailFunctorToEventFlow_injective heq)

theorem RegularCauchyTailFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyTailFunctorDecodeBHist
            (regularCauchyTailFunctorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyTailFunctorUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyTailFunctorUp) ∧
          regularCauchyTailFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyTailFunctorTasteGate_single_carrier_alignment_decode,
      ⟨regularCauchyTailFunctorBHistCarrier⟩,
      ⟨regularCauchyTailFunctorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyTailFunctorUp
