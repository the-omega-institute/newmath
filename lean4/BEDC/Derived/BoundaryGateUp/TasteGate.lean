import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundaryGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundaryGateUp : Type where
  | mk (B Q V S H C P N : BHist) : BoundaryGateUp
  deriving DecidableEq

def boundaryGateEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundaryGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundaryGateEncodeBHist h

def boundaryGateDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundaryGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundaryGateDecodeBHist tail)

private theorem boundaryGateDecode_encode_bhist :
    forall h : BHist, boundaryGateDecodeBHist (boundaryGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundaryGateToEventFlow : BoundaryGateUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundaryGateUp.mk B Q V S H C P N =>
      [[BMark.b0],
        boundaryGateEncodeBHist B,
        [BMark.b1, BMark.b0],
        boundaryGateEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        boundaryGateEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundaryGateEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundaryGateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundaryGateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundaryGateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundaryGateEncodeBHist N]

private def boundaryGateDecodePacket
    (B Q V S H C P N : RawEvent) : BoundaryGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BoundaryGateUp.mk
    (boundaryGateDecodeBHist B)
    (boundaryGateDecodeBHist Q)
    (boundaryGateDecodeBHist V)
    (boundaryGateDecodeBHist S)
    (boundaryGateDecodeBHist H)
    (boundaryGateDecodeBHist C)
    (boundaryGateDecodeBHist P)
    (boundaryGateDecodeBHist N)

def boundaryGateFromEventFlow : EventFlow -> Option BoundaryGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | V :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (boundaryGateDecodePacket
                                                                          B Q V S H C P N)
                                                                  | _ :: _ => none

private theorem boundaryGate_round_trip :
    forall x : BoundaryGateUp,
      boundaryGateFromEventFlow (boundaryGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Q V S H C P N =>
      change
        some
          (boundaryGateDecodePacket
            (boundaryGateEncodeBHist B)
            (boundaryGateEncodeBHist Q)
            (boundaryGateEncodeBHist V)
            (boundaryGateEncodeBHist S)
            (boundaryGateEncodeBHist H)
            (boundaryGateEncodeBHist C)
            (boundaryGateEncodeBHist P)
            (boundaryGateEncodeBHist N)) =
          some (BoundaryGateUp.mk B Q V S H C P N)
      unfold boundaryGateDecodePacket
      rw [boundaryGateDecode_encode_bhist B,
        boundaryGateDecode_encode_bhist Q,
        boundaryGateDecode_encode_bhist V,
        boundaryGateDecode_encode_bhist S,
        boundaryGateDecode_encode_bhist H,
        boundaryGateDecode_encode_bhist C,
        boundaryGateDecode_encode_bhist P,
        boundaryGateDecode_encode_bhist N]

private theorem boundaryGateToEventFlow_injective {x y : BoundaryGateUp} :
    boundaryGateToEventFlow x = boundaryGateToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundaryGateFromEventFlow (boundaryGateToEventFlow x) =
        boundaryGateFromEventFlow (boundaryGateToEventFlow y) :=
    congrArg boundaryGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundaryGate_round_trip x).symm
      (Eq.trans hread (boundaryGate_round_trip y)))

def boundaryGateFields : BoundaryGateUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundaryGateUp.mk B Q V S H C P N => [B, Q, V, S, H, C, P, N]

private theorem boundaryGate_field_faithful :
    forall x y : BoundaryGateUp, boundaryGateFields x = boundaryGateFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 Q1 V1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 Q2 V2 S2 H2 C2 P2 N2 =>
          injection hfields with hB hTail0
          injection hTail0 with hQ hTail1
          injection hTail1 with hV hTail2
          injection hTail2 with hS hTail3
          injection hTail3 with hH hTail4
          injection hTail4 with hC hTail5
          injection hTail5 with hP hTail6
          injection hTail6 with hN _hNil
          cases hB
          cases hQ
          cases hV
          cases hS
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance boundaryGateBHistCarrier : BHistCarrier BoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundaryGateToEventFlow
  fromEventFlow := boundaryGateFromEventFlow

instance boundaryGateChapterTasteGate : ChapterTasteGate BoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundaryGateFromEventFlow (boundaryGateToEventFlow x) = some x
    exact boundaryGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundaryGateToEventFlow_injective heq)

instance boundaryGateFieldFaithful : FieldFaithful BoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundaryGateFields
  field_faithful := boundaryGate_field_faithful

instance boundaryGateNontrivial : Nontrivial BoundaryGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundaryGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundaryGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundaryGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundaryGateChapterTasteGate

theorem BoundaryGateTasteGate_single_carrier_alignment :
    (forall h : BHist, boundaryGateDecodeBHist (boundaryGateEncodeBHist h) = h) ∧
      (forall x : BoundaryGateUp,
        boundaryGateFromEventFlow (boundaryGateToEventFlow x) = some x) ∧
        (forall x y : BoundaryGateUp,
          boundaryGateToEventFlow x = boundaryGateToEventFlow y -> x = y) ∧
          boundaryGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨boundaryGateDecode_encode_bhist,
      boundaryGate_round_trip,
      (fun _ _ heq => boundaryGateToEventFlow_injective heq),
      rfl⟩

theorem BoundaryGate_noninternalization (G : BoundaryGateUp) :
    ∃ B Q V S H C P N : BHist,
      G = BoundaryGateUp.mk B Q V S H C P N ∧
        SemanticNameCert
          (fun row : BHist =>
            hsame row B ∨ hsame row Q ∨ hsame row V ∨ hsame row S ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            hsame row B ∨ hsame row Q ∨ hsame row V ∨ hsame row S ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            hsame row B ∨ hsame row Q ∨ hsame row V ∨ hsame row S ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N)
          hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases G with
  | mk B Q V S H C P N =>
      refine ⟨B, Q, V, S, H, C, P, N, rfl, ?_⟩
      exact {
        core := {
          carrier_inhabited := ⟨B, Or.inl (hsame_refl B)⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other sameRows source
            cases sameRows
            exact source
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.BoundaryGateUp
