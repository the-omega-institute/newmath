import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealOrderUp : Type where
  | mk (S T W D Q R A H C P N : BHist) : CauchyRealOrderUp
  deriving DecidableEq

def cauchyRealOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealOrderEncodeBHist h

def cauchyRealOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealOrderDecodeBHist tail)

private theorem CauchyRealOrderTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealOrderFields : CauchyRealOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealOrderUp.mk S T W D Q R A H C P N => [S, T, W, D, Q, R, A, H, C, P, N]

def cauchyRealOrderToEventFlow : CauchyRealOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealOrderFields x).map cauchyRealOrderEncodeBHist

def cauchyRealOrderFromEventFlow : EventFlow → Option CauchyRealOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | T :: restT =>
          match restT with
          | W :: restW =>
              match restW with
              | D :: restD =>
                  match restD with
                  | Q :: restQ =>
                      match restQ with
                      | R :: restR =>
                          match restR with
                          | A :: restA =>
                              match restA with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (CauchyRealOrderUp.mk
                                                      (cauchyRealOrderDecodeBHist S)
                                                      (cauchyRealOrderDecodeBHist T)
                                                      (cauchyRealOrderDecodeBHist W)
                                                      (cauchyRealOrderDecodeBHist D)
                                                      (cauchyRealOrderDecodeBHist Q)
                                                      (cauchyRealOrderDecodeBHist R)
                                                      (cauchyRealOrderDecodeBHist A)
                                                      (cauchyRealOrderDecodeBHist H)
                                                      (cauchyRealOrderDecodeBHist C)
                                                      (cauchyRealOrderDecodeBHist P)
                                                      (cauchyRealOrderDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyRealOrder_mk_congr
    {S S' T T' W W' D D' Q Q' R R' A A' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hT : T' = T) (hW : W' = W) (hD : D' = D)
    (hQ : Q' = Q) (hR : R' = R) (hA : A' = A) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyRealOrderUp.mk S' T' W' D' Q' R' A' H' C' P' N' =
      CauchyRealOrderUp.mk S T W D Q R A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hT
  cases hW
  cases hD
  cases hQ
  cases hR
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyRealOrderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealOrderUp,
      cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W D Q R A H C P N =>
      exact
        congrArg some
          (cauchyRealOrder_mk_congr
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode S)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode T)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode W)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode D)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode Q)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode R)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode A)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode H)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode C)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode P)
            (CauchyRealOrderTasteGate_single_carrier_alignment_decode N))

private theorem cauchyRealOrderToEventFlow_injective {x y : CauchyRealOrderUp} :
    cauchyRealOrderToEventFlow x = cauchyRealOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) =
        cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow y) :=
    congrArg cauchyRealOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRealOrderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRealOrderTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyRealOrder_fields_faithful :
    ∀ x y : CauchyRealOrderUp, cauchyRealOrderFields x = cauchyRealOrderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ T₁ W₁ D₁ Q₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ W₂ D₂ Q₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
          injection h with hS restS
          injection restS with hT restT
          injection restT with hW restW
          injection restW with hD restD
          injection restD with hQ restQ
          injection restQ with hR restR
          injection restR with hA restA
          injection restA with hH restH
          injection restH with hC restC
          injection restC with hP restP
          injection restP with hN _
          exact
            cauchyRealOrder_mk_congr hS hT hW hD hQ hR hA hH hC hP hN

instance cauchyRealOrderBHistCarrier : BHistCarrier CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealOrderToEventFlow
  fromEventFlow := cauchyRealOrderFromEventFlow

instance cauchyRealOrderChapterTasteGate : ChapterTasteGate CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x
    exact CauchyRealOrderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRealOrderToEventFlow_injective heq)

instance cauchyRealOrderFieldFaithful : FieldFaithful CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealOrderFields
  field_faithful := cauchyRealOrder_fields_faithful

instance cauchyRealOrderNontrivial : Nontrivial CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealOrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRealOrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRealOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealOrderChapterTasteGate

theorem CauchyRealOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist h) = h) ∧
      (∀ x : CauchyRealOrderUp,
        cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x) ∧
      (∀ x y : CauchyRealOrderUp,
        cauchyRealOrderToEventFlow x = cauchyRealOrderToEventFlow y → x = y) ∧
      cauchyRealOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyRealOrderTasteGate_single_carrier_alignment_decode,
      CauchyRealOrderTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => cauchyRealOrderToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRealOrderUp
