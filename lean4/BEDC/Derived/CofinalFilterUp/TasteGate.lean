import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalFilterUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalFilterUp : Type where
  | mk (S T rho lambda Q H C P N : BHist) : CofinalFilterUp
  deriving DecidableEq

def cofinalFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalFilterEncodeBHist h

def cofinalFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalFilterDecodeBHist tail)

private theorem cofinalFilterDecode_encode_bhist :
    ∀ h : BHist, cofinalFilterDecodeBHist (cofinalFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cofinalFilterFields : CofinalFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalFilterUp.mk S T rho lambda Q H C P N => [S, T, rho, lambda, Q, H, C, P, N]

def cofinalFilterToEventFlow : CofinalFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cofinalFilterFields x).map cofinalFilterEncodeBHist

def cofinalFilterFromEventFlow : EventFlow → Option CofinalFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restT =>
      match restT with
      | [] => none
      | T :: restRho =>
          match restRho with
          | [] => none
          | rho :: restLambda =>
              match restLambda with
              | [] => none
              | lambda :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restH =>
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
                                            (CofinalFilterUp.mk
                                              (cofinalFilterDecodeBHist S)
                                              (cofinalFilterDecodeBHist T)
                                              (cofinalFilterDecodeBHist rho)
                                              (cofinalFilterDecodeBHist lambda)
                                              (cofinalFilterDecodeBHist Q)
                                              (cofinalFilterDecodeBHist H)
                                              (cofinalFilterDecodeBHist C)
                                              (cofinalFilterDecodeBHist P)
                                              (cofinalFilterDecodeBHist N))
                                      | _ :: _ => none

private theorem cofinalFilter_round_trip :
    ∀ x : CofinalFilterUp,
      cofinalFilterFromEventFlow (cofinalFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T rho lambda Q H C P N =>
      change
        some
          (CofinalFilterUp.mk
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist S))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist T))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist rho))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist lambda))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist Q))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist H))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist C))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist P))
            (cofinalFilterDecodeBHist (cofinalFilterEncodeBHist N))) =
          some (CofinalFilterUp.mk S T rho lambda Q H C P N)
      rw [cofinalFilterDecode_encode_bhist S, cofinalFilterDecode_encode_bhist T,
        cofinalFilterDecode_encode_bhist rho, cofinalFilterDecode_encode_bhist lambda,
        cofinalFilterDecode_encode_bhist Q, cofinalFilterDecode_encode_bhist H,
        cofinalFilterDecode_encode_bhist C, cofinalFilterDecode_encode_bhist P,
        cofinalFilterDecode_encode_bhist N]

private theorem cofinalFilterToEventFlow_injective {x y : CofinalFilterUp} :
    cofinalFilterToEventFlow x = cofinalFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalFilterFromEventFlow (cofinalFilterToEventFlow x) =
        cofinalFilterFromEventFlow (cofinalFilterToEventFlow y) :=
    congrArg cofinalFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalFilter_round_trip x).symm
      (Eq.trans hread (cofinalFilter_round_trip y)))

private theorem cofinalFilter_fields_faithful :
    ∀ x y : CofinalFilterUp, cofinalFilterFields x = cofinalFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 rho1 lambda1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 rho2 lambda2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cofinalFilterBHistCarrier : BHistCarrier CofinalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalFilterToEventFlow
  fromEventFlow := cofinalFilterFromEventFlow

instance cofinalFilterChapterTasteGate : ChapterTasteGate CofinalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalFilterFromEventFlow (cofinalFilterToEventFlow x) = some x
    exact cofinalFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalFilterToEventFlow_injective heq)

instance cofinalFilterFieldFaithful : FieldFaithful CofinalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cofinalFilterFields
  field_faithful := cofinalFilter_fields_faithful

instance cofinalFilterNontrivial : BEDC.Meta.TasteGate.Nontrivial CofinalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CofinalFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CofinalFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, cofinalFilterDecodeBHist (cofinalFilterEncodeBHist h) = h) ∧
      (∀ x : CofinalFilterUp,
        cofinalFilterFromEventFlow (cofinalFilterToEventFlow x) = some x) ∧
        (∀ x y : CofinalFilterUp,
          cofinalFilterToEventFlow x = cofinalFilterToEventFlow y → x = y) ∧
          cofinalFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cofinalFilterDecode_encode_bhist, cofinalFilter_round_trip,
      (fun _ _ heq => cofinalFilterToEventFlow_injective heq), rfl⟩

end BEDC.Derived.CofinalFilterUp.TasteGate
