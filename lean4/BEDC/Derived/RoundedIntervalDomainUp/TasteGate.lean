import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RoundedIntervalDomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RoundedIntervalDomainUp : Type where
  | mk
      (L U B J W R E H C P N : BHist) :
      RoundedIntervalDomainUp
  deriving DecidableEq

def roundedIntervalDomainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: roundedIntervalDomainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: roundedIntervalDomainEncodeBHist h

def roundedIntervalDomainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (roundedIntervalDomainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (roundedIntervalDomainDecodeBHist tail)

private theorem RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def roundedIntervalDomainFields : RoundedIntervalDomainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RoundedIntervalDomainUp.mk L U B J W R E H C P N =>
      [L, U, B, J, W, R, E, H, C, P, N]

def roundedIntervalDomainToEventFlow : RoundedIntervalDomainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (roundedIntervalDomainFields x).map roundedIntervalDomainEncodeBHist

def roundedIntervalDomainFromEventFlow : EventFlow → Option RoundedIntervalDomainUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restU =>
      match restU with
      | [] => none
      | U :: restB =>
          match restB with
          | [] => none
          | B :: restJ =>
              match restJ with
              | [] => none
              | J :: restW =>
                  match restW with
                  | [] => none
                  | W :: restR =>
                      match restR with
                      | [] => none
                      | R :: restE =>
                          match restE with
                          | [] => none
                          | E :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (RoundedIntervalDomainUp.mk
                                                      (roundedIntervalDomainDecodeBHist L)
                                                      (roundedIntervalDomainDecodeBHist U)
                                                      (roundedIntervalDomainDecodeBHist B)
                                                      (roundedIntervalDomainDecodeBHist J)
                                                      (roundedIntervalDomainDecodeBHist W)
                                                      (roundedIntervalDomainDecodeBHist R)
                                                      (roundedIntervalDomainDecodeBHist E)
                                                      (roundedIntervalDomainDecodeBHist H)
                                                      (roundedIntervalDomainDecodeBHist C)
                                                      (roundedIntervalDomainDecodeBHist P)
                                                      (roundedIntervalDomainDecodeBHist N))
                                              | _ :: _ => none

private theorem RoundedIntervalDomainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RoundedIntervalDomainUp,
      roundedIntervalDomainFromEventFlow (roundedIntervalDomainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U B J W R E H C P N =>
      change
        some
          (RoundedIntervalDomainUp.mk
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist L))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist U))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist B))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist J))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist W))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist R))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist E))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist H))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist C))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist P))
            (roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist N))) =
          some (RoundedIntervalDomainUp.mk L U B J W R E H C P N)
      rw [RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode L,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode U,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode B,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode J,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode W,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode R,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode E,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode H,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode C,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode P,
        RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode N]

private theorem RoundedIntervalDomainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RoundedIntervalDomainUp} :
    roundedIntervalDomainToEventFlow x = roundedIntervalDomainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      roundedIntervalDomainFromEventFlow (roundedIntervalDomainToEventFlow x) =
        roundedIntervalDomainFromEventFlow (roundedIntervalDomainToEventFlow y) :=
    congrArg roundedIntervalDomainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RoundedIntervalDomainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RoundedIntervalDomainTasteGate_single_carrier_alignment_round_trip y)))

instance roundedIntervalDomainBHistCarrier : BHistCarrier RoundedIntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := roundedIntervalDomainToEventFlow
  fromEventFlow := roundedIntervalDomainFromEventFlow

instance roundedIntervalDomainChapterTasteGate : ChapterTasteGate RoundedIntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change roundedIntervalDomainFromEventFlow (roundedIntervalDomainToEventFlow x) = some x
    exact RoundedIntervalDomainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RoundedIntervalDomainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RoundedIntervalDomainTasteGate_single_carrier_alignment :
    (∀ h : BHist, roundedIntervalDomainDecodeBHist (roundedIntervalDomainEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RoundedIntervalDomainUp) ∧
        Nonempty (ChapterTasteGate RoundedIntervalDomainUp) ∧
          roundedIntervalDomainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RoundedIntervalDomainTasteGate_single_carrier_alignment_decode_encode,
      ⟨roundedIntervalDomainBHistCarrier⟩,
      ⟨roundedIntervalDomainChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RoundedIntervalDomainUp
