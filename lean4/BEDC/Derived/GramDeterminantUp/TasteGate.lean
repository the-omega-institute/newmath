import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GramDeterminantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GramDeterminantUp : Type where
  | mk (V I A M D J T R H C P N : BHist) : GramDeterminantUp
  deriving DecidableEq

def gramDeterminantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gramDeterminantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gramDeterminantEncodeBHist h

def gramDeterminantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gramDeterminantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gramDeterminantDecodeBHist tail)

private theorem GramDeterminantTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, gramDeterminantDecodeBHist (gramDeterminantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gramDeterminantFields : GramDeterminantUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GramDeterminantUp.mk V I A M D J T R H C P N => [V, I, A, M, D, J, T, R, H, C, P, N]

def gramDeterminantToEventFlow : GramDeterminantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gramDeterminantFields x).map gramDeterminantEncodeBHist

def gramDeterminantFromEventFlowTail
    (V I A M D J T R H C : RawEvent) : EventFlow → Option GramDeterminantUp
  -- BEDC touchpoint anchor: BHist BMark
  | P :: restP =>
      match restP with
      | N :: rest =>
          match rest with
          | [] =>
              some
                (GramDeterminantUp.mk
                  (gramDeterminantDecodeBHist V)
                  (gramDeterminantDecodeBHist I)
                  (gramDeterminantDecodeBHist A)
                  (gramDeterminantDecodeBHist M)
                  (gramDeterminantDecodeBHist D)
                  (gramDeterminantDecodeBHist J)
                  (gramDeterminantDecodeBHist T)
                  (gramDeterminantDecodeBHist R)
                  (gramDeterminantDecodeBHist H)
                  (gramDeterminantDecodeBHist C)
                  (gramDeterminantDecodeBHist P)
                  (gramDeterminantDecodeBHist N))
          | _ :: _ => none
      | [] => none
  | [] => none

def gramDeterminantFromEventFlow : EventFlow → Option GramDeterminantUp
  -- BEDC touchpoint anchor: BHist BMark
  | V :: restV =>
      match restV with
      | I :: restI =>
          match restI with
          | A :: restA =>
              match restA with
              | M :: restM =>
                  match restM with
                  | D :: restD =>
                      match restD with
                      | J :: restJ =>
                          match restJ with
                          | T :: restT =>
                              match restT with
                              | R :: restR =>
                                  match restR with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          gramDeterminantFromEventFlowTail V I A M D J T R H C restC
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

private theorem gramDeterminant_mk_congr
    {V V' I I' A A' M M' D D' J J' T T' R R' H H' C C' P P' N N' : BHist}
    (hV : V' = V) (hI : I' = I) (hA : A' = A) (hM : M' = M)
    (hD : D' = D) (hJ : J' = J) (hT : T' = T) (hR : R' = R)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    GramDeterminantUp.mk V' I' A' M' D' J' T' R' H' C' P' N' =
      GramDeterminantUp.mk V I A M D J T R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hV
  cases hI
  cases hA
  cases hM
  cases hD
  cases hJ
  cases hT
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem GramDeterminantTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GramDeterminantUp,
      gramDeterminantFromEventFlow (gramDeterminantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V I A M D J T R H C P N =>
      exact
        congrArg some
          (gramDeterminant_mk_congr
            (GramDeterminantTasteGate_single_carrier_alignment_decode V)
            (GramDeterminantTasteGate_single_carrier_alignment_decode I)
            (GramDeterminantTasteGate_single_carrier_alignment_decode A)
            (GramDeterminantTasteGate_single_carrier_alignment_decode M)
            (GramDeterminantTasteGate_single_carrier_alignment_decode D)
            (GramDeterminantTasteGate_single_carrier_alignment_decode J)
            (GramDeterminantTasteGate_single_carrier_alignment_decode T)
            (GramDeterminantTasteGate_single_carrier_alignment_decode R)
            (GramDeterminantTasteGate_single_carrier_alignment_decode H)
            (GramDeterminantTasteGate_single_carrier_alignment_decode C)
            (GramDeterminantTasteGate_single_carrier_alignment_decode P)
            (GramDeterminantTasteGate_single_carrier_alignment_decode N))

private theorem gramDeterminantToEventFlow_injective {x y : GramDeterminantUp} :
    gramDeterminantToEventFlow x = gramDeterminantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gramDeterminantFromEventFlow (gramDeterminantToEventFlow x) =
        gramDeterminantFromEventFlow (gramDeterminantToEventFlow y) :=
    congrArg gramDeterminantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GramDeterminantTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (GramDeterminantTasteGate_single_carrier_alignment_round_trip y)))

private theorem gramDeterminant_field_faithful :
    ∀ x y : GramDeterminantUp, gramDeterminantFields x = gramDeterminantFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V I A M D J T R H C P N =>
      cases y with
      | mk V' I' A' M' D' J' T' R' H' C' P' N' =>
          cases hfields
          rfl

instance gramDeterminantBHistCarrier : BHistCarrier GramDeterminantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gramDeterminantToEventFlow
  fromEventFlow := gramDeterminantFromEventFlow

instance gramDeterminantChapterTasteGate : ChapterTasteGate GramDeterminantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gramDeterminantFromEventFlow (gramDeterminantToEventFlow x) = some x
    exact GramDeterminantTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gramDeterminantToEventFlow_injective heq)

instance gramDeterminantFieldFaithful : FieldFaithful GramDeterminantUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gramDeterminantFields
  field_faithful := gramDeterminant_field_faithful

instance gramDeterminantNontrivial :
    BEDC.Meta.TasteGate.Nontrivial GramDeterminantUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GramDeterminantUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GramDeterminantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GramDeterminantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gramDeterminantChapterTasteGate

theorem GramDeterminantTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GramDeterminantUp) ∧
      Nonempty (BHistCarrier GramDeterminantUp) ∧
        Nonempty (FieldFaithful GramDeterminantUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial GramDeterminantUp) ∧
            gramDeterminantDecodeBHist (gramDeterminantEncodeBHist BHist.Empty) =
              BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨gramDeterminantChapterTasteGate⟩
  constructor
  · exact ⟨gramDeterminantBHistCarrier⟩
  constructor
  · exact ⟨gramDeterminantFieldFaithful⟩
  constructor
  · exact ⟨gramDeterminantNontrivial⟩
  · rfl

end BEDC.Derived.GramDeterminantUp
