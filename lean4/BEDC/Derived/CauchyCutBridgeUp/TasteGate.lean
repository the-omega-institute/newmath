import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCutBridgeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCutBridgeUp : Type where
  | mk (Q L D W E H C P N : BHist) : CauchyCutBridgeUp
  deriving DecidableEq

def cauchyCutBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCutBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCutBridgeEncodeBHist h

def cauchyCutBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCutBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCutBridgeDecodeBHist tail)

private theorem CauchyCutBridgeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCutBridgeFields : CauchyCutBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCutBridgeUp.mk Q L D W E H C P N => [Q, L, D, W, E, H, C, P, N]

def cauchyCutBridgeToEventFlow : CauchyCutBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyCutBridgeEncodeBHist (cauchyCutBridgeFields x)

def cauchyCutBridgeFromEventFlow : EventFlow → Option CauchyCutBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: restQ =>
      match restQ with
      | [] => none
      | L :: restL =>
          match restL with
          | [] => none
          | D :: restD =>
              match restD with
              | [] => none
              | W :: restW =>
                  match restW with
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
                                            (CauchyCutBridgeUp.mk
                                              (cauchyCutBridgeDecodeBHist Q)
                                              (cauchyCutBridgeDecodeBHist L)
                                              (cauchyCutBridgeDecodeBHist D)
                                              (cauchyCutBridgeDecodeBHist W)
                                              (cauchyCutBridgeDecodeBHist E)
                                              (cauchyCutBridgeDecodeBHist H)
                                              (cauchyCutBridgeDecodeBHist C)
                                              (cauchyCutBridgeDecodeBHist P)
                                              (cauchyCutBridgeDecodeBHist N))
                                      | _ :: _ => none

private theorem CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCutBridgeUp,
      cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q L D W E H C P N =>
      change
        some
          (CauchyCutBridgeUp.mk
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist Q))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist L))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist D))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist W))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist E))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist H))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist C))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist P))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist N))) =
          some (CauchyCutBridgeUp.mk Q L D W E H C P N)
      rw [CauchyCutBridgeTasteGate_single_carrier_alignment_decode Q,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode L,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode D,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode W,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode E,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode H,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode C,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode P,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCutBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCutBridgeUp} :
    cauchyCutBridgeToEventFlow x = cauchyCutBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow x) =
        cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow y) :=
    congrArg cauchyCutBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCutBridgeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyCutBridgeUp, cauchyCutBridgeFields x = cauchyCutBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ L₁ D₁ W₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ L₂ D₂ W₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyCutBridgeBHistCarrier : BHistCarrier CauchyCutBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCutBridgeToEventFlow
  fromEventFlow := cauchyCutBridgeFromEventFlow

instance cauchyCutBridgeChapterTasteGate : ChapterTasteGate CauchyCutBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow x) = some x
    exact CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCutBridgeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCutBridgeFieldFaithful : FieldFaithful CauchyCutBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCutBridgeFields
  field_faithful := CauchyCutBridgeTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate CauchyCutBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCutBridgeChapterTasteGate

theorem CauchyCutBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist h) = h) ∧
      (∀ x : CauchyCutBridgeUp,
        cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow x) = some x) ∧
        (∀ x y : CauchyCutBridgeUp,
          cauchyCutBridgeToEventFlow x = cauchyCutBridgeToEventFlow y → x = y) ∧
          cauchyCutBridgeFields
              (CauchyCutBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCutBridgeTasteGate_single_carrier_alignment_decode,
      CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => CauchyCutBridgeTasteGate_single_carrier_alignment_toEventFlow_injective h),
      rfl⟩

end BEDC.Derived.CauchyCutBridgeUp.TasteGate
