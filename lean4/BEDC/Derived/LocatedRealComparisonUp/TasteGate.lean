import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealComparisonUp : Type where
  | mk (L0 L1 W R0 R1 D0 D1 B A H C P N : BHist) : LocatedRealComparisonUp
  deriving DecidableEq

def locatedRealComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealComparisonEncodeBHist h

def locatedRealComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealComparisonDecodeBHist tail)

private theorem LocatedRealComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealComparisonFields : LocatedRealComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealComparisonUp.mk L0 L1 W R0 R1 D0 D1 B A H C P N =>
      [L0, L1, W, R0, R1, D0, D1, B, A, H, C, P, N]

def locatedRealComparisonToEventFlow : LocatedRealComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealComparisonFields x).map locatedRealComparisonEncodeBHist

def locatedRealComparisonFromEventFlow : EventFlow → Option LocatedRealComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | L0 :: restL0 =>
      match restL0 with
      | L1 :: restL1 =>
          match restL1 with
          | W :: restW =>
              match restW with
              | R0 :: restR0 =>
                  match restR0 with
                  | R1 :: restR1 =>
                      match restR1 with
                      | D0 :: restD0 =>
                          match restD0 with
                          | D1 :: restD1 =>
                              match restD1 with
                              | B :: restB =>
                                  match restB with
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
                                                            (LocatedRealComparisonUp.mk
                                                              (locatedRealComparisonDecodeBHist L0)
                                                              (locatedRealComparisonDecodeBHist L1)
                                                              (locatedRealComparisonDecodeBHist W)
                                                              (locatedRealComparisonDecodeBHist R0)
                                                              (locatedRealComparisonDecodeBHist R1)
                                                              (locatedRealComparisonDecodeBHist D0)
                                                              (locatedRealComparisonDecodeBHist D1)
                                                              (locatedRealComparisonDecodeBHist B)
                                                              (locatedRealComparisonDecodeBHist A)
                                                              (locatedRealComparisonDecodeBHist H)
                                                              (locatedRealComparisonDecodeBHist C)
                                                              (locatedRealComparisonDecodeBHist P)
                                                              (locatedRealComparisonDecodeBHist N))
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
      | [] => none
  | [] => none

private theorem locatedRealComparison_mk_congr
    {L0 L0' L1 L1' W W' R0 R0' R1 R1' D0 D0' D1 D1' B B' A A' H H'
      C C' P P' N N' : BHist}
    (hL0 : L0' = L0) (hL1 : L1' = L1) (hW : W' = W) (hR0 : R0' = R0)
    (hR1 : R1' = R1) (hD0 : D0' = D0) (hD1 : D1' = D1) (hB : B' = B)
    (hA : A' = A) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    LocatedRealComparisonUp.mk L0' L1' W' R0' R1' D0' D1' B' A' H' C' P' N' =
      LocatedRealComparisonUp.mk L0 L1 W R0 R1 D0 D1 B A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL0
  cases hL1
  cases hW
  cases hR0
  cases hR1
  cases hD0
  cases hD1
  cases hB
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealComparisonUp,
      locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L0 L1 W R0 R1 D0 D1 B A H C P N =>
      exact
        congrArg some
          (locatedRealComparison_mk_congr
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode L0)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode L1)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode W)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode R0)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode R1)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode D0)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode D1)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode B)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode A)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode H)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode C)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode P)
            (LocatedRealComparisonTasteGate_single_carrier_alignment_decode N))

private theorem locatedRealComparisonToEventFlow_injective {x y : LocatedRealComparisonUp} :
    locatedRealComparisonToEventFlow x = locatedRealComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) =
        locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow y) :=
    congrArg locatedRealComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip y)))

private theorem locatedRealComparison_fields_faithful :
    ∀ x y : LocatedRealComparisonUp,
      locatedRealComparisonFields x = locatedRealComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk L0₁ L1₁ W₁ R0₁ R1₁ D0₁ D1₁ B₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L0₂ L1₂ W₂ R0₂ R1₂ D0₂ D1₂ B₂ A₂ H₂ C₂ P₂ N₂ =>
          injection h with hL0 restL0
          injection restL0 with hL1 restL1
          injection restL1 with hW restW
          injection restW with hR0 restR0
          injection restR0 with hR1 restR1
          injection restR1 with hD0 restD0
          injection restD0 with hD1 restD1
          injection restD1 with hB restB
          injection restB with hA restA
          injection restA with hH restH
          injection restH with hC restC
          injection restC with hP restP
          injection restP with hN _
          exact
            locatedRealComparison_mk_congr hL0 hL1 hW hR0 hR1 hD0 hD1 hB hA hH hC
              hP hN

instance locatedRealComparisonBHistCarrier : BHistCarrier LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealComparisonToEventFlow
  fromEventFlow := locatedRealComparisonFromEventFlow

instance locatedRealComparisonChapterTasteGate :
    ChapterTasteGate LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) = some x
    exact LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealComparisonToEventFlow_injective heq)

instance locatedRealComparisonFieldFaithful : FieldFaithful LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealComparisonFields
  field_faithful := locatedRealComparison_fields_faithful

instance locatedRealComparisonNontrivial : Nontrivial LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedRealComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealComparisonChapterTasteGate

theorem LocatedRealComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist h) = h) ∧
      (∀ x : LocatedRealComparisonUp,
        locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) = some x) ∧
      (∀ x y : LocatedRealComparisonUp,
        locatedRealComparisonToEventFlow x = locatedRealComparisonToEventFlow y → x = y) ∧
      locatedRealComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedRealComparisonTasteGate_single_carrier_alignment_decode,
      LocatedRealComparisonTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => locatedRealComparisonToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedRealComparisonUp
