import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicDifferentiationBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicDifferentiationBasisUp : Type where
  | mk (D L I C R E F H K P N : BHist) : DyadicDifferentiationBasisUp
  deriving DecidableEq

def dyadicDifferentiationBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicDifferentiationBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicDifferentiationBasisEncodeBHist h

def dyadicDifferentiationBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicDifferentiationBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicDifferentiationBasisDecodeBHist tail)

private theorem dyadicDifferentiationBasisDecode_encode_bhist :
    ∀ h : BHist,
      dyadicDifferentiationBasisDecodeBHist
        (dyadicDifferentiationBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def dyadicDifferentiationBasisDecodePacket
    (D L I C R E F H K P N : RawEvent) : DyadicDifferentiationBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DyadicDifferentiationBasisUp.mk
    (dyadicDifferentiationBasisDecodeBHist D)
    (dyadicDifferentiationBasisDecodeBHist L)
    (dyadicDifferentiationBasisDecodeBHist I)
    (dyadicDifferentiationBasisDecodeBHist C)
    (dyadicDifferentiationBasisDecodeBHist R)
    (dyadicDifferentiationBasisDecodeBHist E)
    (dyadicDifferentiationBasisDecodeBHist F)
    (dyadicDifferentiationBasisDecodeBHist H)
    (dyadicDifferentiationBasisDecodeBHist K)
    (dyadicDifferentiationBasisDecodeBHist P)
    (dyadicDifferentiationBasisDecodeBHist N)

def dyadicDifferentiationBasisToEventFlow : DyadicDifferentiationBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicDifferentiationBasisUp.mk D L I C R E F H K P N =>
      [dyadicDifferentiationBasisEncodeBHist D,
        dyadicDifferentiationBasisEncodeBHist L,
        dyadicDifferentiationBasisEncodeBHist I,
        dyadicDifferentiationBasisEncodeBHist C,
        dyadicDifferentiationBasisEncodeBHist R,
        dyadicDifferentiationBasisEncodeBHist E,
        dyadicDifferentiationBasisEncodeBHist F,
        dyadicDifferentiationBasisEncodeBHist H,
        dyadicDifferentiationBasisEncodeBHist K,
        dyadicDifferentiationBasisEncodeBHist P,
        dyadicDifferentiationBasisEncodeBHist N]

def dyadicDifferentiationBasisFromEventFlow :
    EventFlow → Option DyadicDifferentiationBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: restL =>
      match restL with
      | [] => none
      | L :: restI =>
          match restI with
          | [] => none
          | I :: restC =>
              match restC with
              | [] => none
              | C :: restR =>
                  match restR with
                  | [] => none
                  | R :: restE =>
                      match restE with
                      | [] => none
                      | E :: restF =>
                          match restF with
                          | [] => none
                          | F :: restH =>
                              match restH with
                              | [] => none
                              | H :: restK =>
                                  match restK with
                                  | [] => none
                                  | K :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (dyadicDifferentiationBasisDecodePacket
                                                      D L I C R E F H K P N)
                                              | _ :: _ => none

private theorem dyadicDifferentiationBasis_round_trip :
    ∀ x : DyadicDifferentiationBasisUp,
      dyadicDifferentiationBasisFromEventFlow
        (dyadicDifferentiationBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D L I C R E F H K P N =>
      change
        some
            (dyadicDifferentiationBasisDecodePacket
              (dyadicDifferentiationBasisEncodeBHist D)
              (dyadicDifferentiationBasisEncodeBHist L)
              (dyadicDifferentiationBasisEncodeBHist I)
              (dyadicDifferentiationBasisEncodeBHist C)
              (dyadicDifferentiationBasisEncodeBHist R)
              (dyadicDifferentiationBasisEncodeBHist E)
              (dyadicDifferentiationBasisEncodeBHist F)
              (dyadicDifferentiationBasisEncodeBHist H)
              (dyadicDifferentiationBasisEncodeBHist K)
              (dyadicDifferentiationBasisEncodeBHist P)
              (dyadicDifferentiationBasisEncodeBHist N)) =
          some (DyadicDifferentiationBasisUp.mk D L I C R E F H K P N)
      unfold dyadicDifferentiationBasisDecodePacket
      rw [dyadicDifferentiationBasisDecode_encode_bhist D,
        dyadicDifferentiationBasisDecode_encode_bhist L,
        dyadicDifferentiationBasisDecode_encode_bhist I,
        dyadicDifferentiationBasisDecode_encode_bhist C,
        dyadicDifferentiationBasisDecode_encode_bhist R,
        dyadicDifferentiationBasisDecode_encode_bhist E,
        dyadicDifferentiationBasisDecode_encode_bhist F,
        dyadicDifferentiationBasisDecode_encode_bhist H,
        dyadicDifferentiationBasisDecode_encode_bhist K,
        dyadicDifferentiationBasisDecode_encode_bhist P,
        dyadicDifferentiationBasisDecode_encode_bhist N]

theorem DyadicDifferentiationBasisToEventFlow_injective
    {x y : DyadicDifferentiationBasisUp} :
    dyadicDifferentiationBasisToEventFlow x =
      dyadicDifferentiationBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicDifferentiationBasisFromEventFlow
          (dyadicDifferentiationBasisToEventFlow x) =
        dyadicDifferentiationBasisFromEventFlow
          (dyadicDifferentiationBasisToEventFlow y) :=
    congrArg dyadicDifferentiationBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicDifferentiationBasis_round_trip x).symm
      (Eq.trans hread (dyadicDifferentiationBasis_round_trip y)))

instance dyadicDifferentiationBasisBHistCarrier :
    BHistCarrier DyadicDifferentiationBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicDifferentiationBasisToEventFlow
  fromEventFlow := dyadicDifferentiationBasisFromEventFlow

instance dyadicDifferentiationBasisChapterTasteGate :
    ChapterTasteGate DyadicDifferentiationBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicDifferentiationBasisFromEventFlow
        (dyadicDifferentiationBasisToEventFlow x) = some x
    exact dyadicDifferentiationBasis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicDifferentiationBasisToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicDifferentiationBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicDifferentiationBasisChapterTasteGate

theorem DyadicDifferentiationBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicDifferentiationBasisDecodeBHist
        (dyadicDifferentiationBasisEncodeBHist h) = h) ∧
      (∀ x : DyadicDifferentiationBasisUp,
        dyadicDifferentiationBasisFromEventFlow
          (dyadicDifferentiationBasisToEventFlow x) = some x) ∧
        (∀ x y : DyadicDifferentiationBasisUp,
          dyadicDifferentiationBasisToEventFlow x =
            dyadicDifferentiationBasisToEventFlow y → x = y) ∧
          dyadicDifferentiationBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicDifferentiationBasisDecode_encode_bhist
  · constructor
    · intro x
      exact dyadicDifferentiationBasis_round_trip x
    · constructor
      · intro x y heq
        exact DyadicDifferentiationBasisToEventFlow_injective heq
      · rfl

end BEDC.Derived.DyadicDifferentiationBasisUp
