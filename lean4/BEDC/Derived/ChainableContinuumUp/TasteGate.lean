import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChainableContinuumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChainableContinuumUp : Type where
  | mk (K C L M T R H P N : BHist) : ChainableContinuumUp
  deriving DecidableEq

def chainableContinuumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: chainableContinuumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: chainableContinuumEncodeBHist h

def chainableContinuumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (chainableContinuumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (chainableContinuumDecodeBHist tail)

private theorem chainableContinuumDecode_encode_bhist :
    ∀ h : BHist, chainableContinuumDecodeBHist (chainableContinuumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def chainableContinuumFields : ChainableContinuumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChainableContinuumUp.mk K C L M T R H P N => [K, C, L, M, T, R, H, P, N]

def chainableContinuumToEventFlow : ChainableContinuumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (chainableContinuumFields x).map chainableContinuumEncodeBHist

def chainableContinuumFromEventFlow : EventFlow → Option ChainableContinuumUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ChainableContinuumUp.mk
                                              (chainableContinuumDecodeBHist K)
                                              (chainableContinuumDecodeBHist C)
                                              (chainableContinuumDecodeBHist L)
                                              (chainableContinuumDecodeBHist M)
                                              (chainableContinuumDecodeBHist T)
                                              (chainableContinuumDecodeBHist R)
                                              (chainableContinuumDecodeBHist H)
                                              (chainableContinuumDecodeBHist P)
                                              (chainableContinuumDecodeBHist N))
                                      | _ :: _ => none

private theorem chainableContinuum_mk_congr
    {K K' C C' L L' M M' T T' R R' H H' P P' N N' : BHist}
    (hK : K' = K) (hC : C' = C) (hL : L' = L) (hM : M' = M)
    (hT : T' = T) (hR : R' = R) (hH : H' = H) (hP : P' = P)
    (hN : N' = N) :
    ChainableContinuumUp.mk K' C' L' M' T' R' H' P' N' =
      ChainableContinuumUp.mk K C L M T R H P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hC
  cases hL
  cases hM
  cases hT
  cases hR
  cases hH
  cases hP
  cases hN
  rfl

private theorem chainableContinuum_round_trip :
    ∀ x : ChainableContinuumUp,
      chainableContinuumFromEventFlow (chainableContinuumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K C L M T R H P N =>
      change
        some
          (ChainableContinuumUp.mk
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist K))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist C))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist L))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist M))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist T))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist R))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist H))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist P))
            (chainableContinuumDecodeBHist (chainableContinuumEncodeBHist N))) =
          some (ChainableContinuumUp.mk K C L M T R H P N)
      exact
        congrArg some
          (chainableContinuum_mk_congr
            (chainableContinuumDecode_encode_bhist K)
            (chainableContinuumDecode_encode_bhist C)
            (chainableContinuumDecode_encode_bhist L)
            (chainableContinuumDecode_encode_bhist M)
            (chainableContinuumDecode_encode_bhist T)
            (chainableContinuumDecode_encode_bhist R)
            (chainableContinuumDecode_encode_bhist H)
            (chainableContinuumDecode_encode_bhist P)
            (chainableContinuumDecode_encode_bhist N))

private theorem chainableContinuumToEventFlow_injective {x y : ChainableContinuumUp} :
    chainableContinuumToEventFlow x = chainableContinuumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk K C L M T R H P N =>
      cases y with
      | mk K' C' L' M' T' R' H' P' N' =>
          change
            [chainableContinuumEncodeBHist K, chainableContinuumEncodeBHist C,
              chainableContinuumEncodeBHist L, chainableContinuumEncodeBHist M,
              chainableContinuumEncodeBHist T, chainableContinuumEncodeBHist R,
              chainableContinuumEncodeBHist H, chainableContinuumEncodeBHist P,
              chainableContinuumEncodeBHist N] =
                [chainableContinuumEncodeBHist K', chainableContinuumEncodeBHist C',
                  chainableContinuumEncodeBHist L', chainableContinuumEncodeBHist M',
                  chainableContinuumEncodeBHist T', chainableContinuumEncodeBHist R',
                  chainableContinuumEncodeBHist H', chainableContinuumEncodeBHist P',
                  chainableContinuumEncodeBHist N'] at heq
          injection heq with hK htail0
          injection htail0 with hC htail1
          injection htail1 with hL htail2
          injection htail2 with hM htail3
          injection htail3 with hT htail4
          injection htail4 with hR htail5
          injection htail5 with hH htail6
          injection htail6 with hP htail7
          injection htail7 with hN _hNil
          have kEq : K = K' := by
            have decoded := congrArg chainableContinuumDecodeBHist hK
            rw [chainableContinuumDecode_encode_bhist K,
              chainableContinuumDecode_encode_bhist K'] at decoded
            exact decoded
          have cEq : C = C' := by
            have decoded := congrArg chainableContinuumDecodeBHist hC
            rw [chainableContinuumDecode_encode_bhist C,
              chainableContinuumDecode_encode_bhist C'] at decoded
            exact decoded
          have lEq : L = L' := by
            have decoded := congrArg chainableContinuumDecodeBHist hL
            rw [chainableContinuumDecode_encode_bhist L,
              chainableContinuumDecode_encode_bhist L'] at decoded
            exact decoded
          have mEq : M = M' := by
            have decoded := congrArg chainableContinuumDecodeBHist hM
            rw [chainableContinuumDecode_encode_bhist M,
              chainableContinuumDecode_encode_bhist M'] at decoded
            exact decoded
          have tEq : T = T' := by
            have decoded := congrArg chainableContinuumDecodeBHist hT
            rw [chainableContinuumDecode_encode_bhist T,
              chainableContinuumDecode_encode_bhist T'] at decoded
            exact decoded
          have rEq : R = R' := by
            have decoded := congrArg chainableContinuumDecodeBHist hR
            rw [chainableContinuumDecode_encode_bhist R,
              chainableContinuumDecode_encode_bhist R'] at decoded
            exact decoded
          have hEq : H = H' := by
            have decoded := congrArg chainableContinuumDecodeBHist hH
            rw [chainableContinuumDecode_encode_bhist H,
              chainableContinuumDecode_encode_bhist H'] at decoded
            exact decoded
          have pEq : P = P' := by
            have decoded := congrArg chainableContinuumDecodeBHist hP
            rw [chainableContinuumDecode_encode_bhist P,
              chainableContinuumDecode_encode_bhist P'] at decoded
            exact decoded
          have nEq : N = N' := by
            have decoded := congrArg chainableContinuumDecodeBHist hN
            rw [chainableContinuumDecode_encode_bhist N,
              chainableContinuumDecode_encode_bhist N'] at decoded
            exact decoded
          cases kEq
          cases cEq
          cases lEq
          cases mEq
          cases tEq
          cases rEq
          cases hEq
          cases pEq
          cases nEq
          rfl

private theorem chainableContinuum_fields_faithful :
    ∀ x y : ChainableContinuumUp, chainableContinuumFields x = chainableContinuumFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K C L M T R H P N =>
      cases y with
      | mk K' C' L' M' T' R' H' P' N' =>
          injection hfields with hK htail0
          injection htail0 with hC htail1
          injection htail1 with hL htail2
          injection htail2 with hM htail3
          injection htail3 with hT htail4
          injection htail4 with hR htail5
          injection htail5 with hH htail6
          injection htail6 with hP htail7
          injection htail7 with hN _hNil
          cases hK
          cases hC
          cases hL
          cases hM
          cases hT
          cases hR
          cases hH
          cases hP
          cases hN
          rfl

instance chainableContinuumBHistCarrier : BHistCarrier ChainableContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := chainableContinuumToEventFlow
  fromEventFlow := chainableContinuumFromEventFlow

instance chainableContinuumChapterTasteGate : ChapterTasteGate ChainableContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := chainableContinuum_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (chainableContinuumToEventFlow_injective heq)

instance chainableContinuumFieldFaithful : FieldFaithful ChainableContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := chainableContinuumFields
  field_faithful := chainableContinuum_fields_faithful

instance chainableContinuumNontrivial : Nontrivial ChainableContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChainableContinuumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ChainableContinuumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ChainableContinuumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  chainableContinuumChapterTasteGate

theorem ChainableContinuumTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ChainableContinuumUp) ∧
      Nonempty (FieldFaithful ChainableContinuumUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ChainableContinuumUp) ∧
          (∀ h : BHist, chainableContinuumDecodeBHist (chainableContinuumEncodeBHist h) = h) ∧
            (∀ x : ChainableContinuumUp,
              chainableContinuumFromEventFlow (chainableContinuumToEventFlow x) = some x) ∧
              (∀ x y : ChainableContinuumUp,
                chainableContinuumToEventFlow x = chainableContinuumToEventFlow y → x = y) ∧
                chainableContinuumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨chainableContinuumChapterTasteGate⟩,
      ⟨chainableContinuumFieldFaithful⟩,
      ⟨chainableContinuumNontrivial⟩,
      chainableContinuumDecode_encode_bhist,
      chainableContinuum_round_trip,
      (fun _ _ heq => chainableContinuumToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ChainableContinuumUp
