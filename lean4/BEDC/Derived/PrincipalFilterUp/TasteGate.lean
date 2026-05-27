import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrincipalFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrincipalFilterUp : Type where
  | mk (G U M R H C P N : BHist) : PrincipalFilterUp
  deriving DecidableEq

def principalFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: principalFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: principalFilterEncodeBHist h

def principalFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (principalFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (principalFilterDecodeBHist tail)

private theorem principalFilterDecode_encode_bhist :
    ∀ h : BHist, principalFilterDecodeBHist (principalFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def principalFilterFields : PrincipalFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrincipalFilterUp.mk G U M R H C P N => [G, U, M, R, H, C, P, N]

def principalFilterToEventFlow : PrincipalFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (principalFilterFields x).map principalFilterEncodeBHist

def principalFilterFromEventFlow : EventFlow → Option PrincipalFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | G :: restU =>
      match restU with
      | [] => none
      | U :: restM =>
          match restM with
          | [] => none
          | M :: restR =>
              match restR with
              | [] => none
              | R :: restH =>
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
                                        (PrincipalFilterUp.mk
                                          (principalFilterDecodeBHist G)
                                          (principalFilterDecodeBHist U)
                                          (principalFilterDecodeBHist M)
                                          (principalFilterDecodeBHist R)
                                          (principalFilterDecodeBHist H)
                                          (principalFilterDecodeBHist C)
                                          (principalFilterDecodeBHist P)
                                          (principalFilterDecodeBHist N))
                                  | _ :: _ => none

private theorem principalFilter_round_trip :
    ∀ x : PrincipalFilterUp,
      principalFilterFromEventFlow (principalFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G U M R H C P N =>
      change
        some
          (PrincipalFilterUp.mk
            (principalFilterDecodeBHist (principalFilterEncodeBHist G))
            (principalFilterDecodeBHist (principalFilterEncodeBHist U))
            (principalFilterDecodeBHist (principalFilterEncodeBHist M))
            (principalFilterDecodeBHist (principalFilterEncodeBHist R))
            (principalFilterDecodeBHist (principalFilterEncodeBHist H))
            (principalFilterDecodeBHist (principalFilterEncodeBHist C))
            (principalFilterDecodeBHist (principalFilterEncodeBHist P))
            (principalFilterDecodeBHist (principalFilterEncodeBHist N))) =
          some (PrincipalFilterUp.mk G U M R H C P N)
      rw [principalFilterDecode_encode_bhist G, principalFilterDecode_encode_bhist U,
        principalFilterDecode_encode_bhist M, principalFilterDecode_encode_bhist R,
        principalFilterDecode_encode_bhist H, principalFilterDecode_encode_bhist C,
        principalFilterDecode_encode_bhist P, principalFilterDecode_encode_bhist N]

private theorem principalFilterToEventFlow_injective {x y : PrincipalFilterUp} :
    principalFilterToEventFlow x = principalFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      principalFilterFromEventFlow (principalFilterToEventFlow x) =
        principalFilterFromEventFlow (principalFilterToEventFlow y) :=
    congrArg principalFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (principalFilter_round_trip x).symm
      (Eq.trans hread (principalFilter_round_trip y)))

private theorem principalFilter_fields_faithful :
    ∀ x y : PrincipalFilterUp, principalFilterFields x = principalFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 U1 M1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk G2 U2 M2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance principalFilterBHistCarrier : BHistCarrier PrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := principalFilterToEventFlow
  fromEventFlow := principalFilterFromEventFlow

instance principalFilterChapterTasteGate : ChapterTasteGate PrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change principalFilterFromEventFlow (principalFilterToEventFlow x) = some x
    exact principalFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (principalFilterToEventFlow_injective heq)

instance principalFilterFieldFaithful : FieldFaithful PrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := principalFilterFields
  field_faithful := principalFilter_fields_faithful

instance principalFilterNontrivial : BEDC.Meta.TasteGate.Nontrivial PrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PrincipalFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PrincipalFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PrincipalFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  principalFilterChapterTasteGate

theorem PrincipalFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, principalFilterDecodeBHist (principalFilterEncodeBHist h) = h) ∧
      (∀ x : PrincipalFilterUp,
        principalFilterFromEventFlow (principalFilterToEventFlow x) = some x) ∧
        (∀ x y : PrincipalFilterUp,
          principalFilterToEventFlow x = principalFilterToEventFlow y → x = y) ∧
          principalFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨principalFilterDecode_encode_bhist, principalFilter_round_trip,
      (fun _ _ heq => principalFilterToEventFlow_injective heq), rfl⟩

end BEDC.Derived.PrincipalFilterUp
