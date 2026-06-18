import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EuclideanAlgorithmUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EuclideanAlgorithmUp : Type where
  | mk (I S B T Z H C P N : BHist) : EuclideanAlgorithmUp
  deriving DecidableEq

def euclideanAlgorithmEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: euclideanAlgorithmEncodeBHist h
  | BHist.e1 h => BMark.b1 :: euclideanAlgorithmEncodeBHist h

def euclideanAlgorithmDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (euclideanAlgorithmDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (euclideanAlgorithmDecodeBHist tail)

private theorem euclideanAlgorithm_decode_encode_bhist :
    ∀ h : BHist, euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def euclideanAlgorithmFields : EuclideanAlgorithmUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EuclideanAlgorithmUp.mk I S B T Z H C P N => [I, S, B, T, Z, H, C, P, N]

def euclideanAlgorithmToEventFlow : EuclideanAlgorithmUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EuclideanAlgorithmUp.mk I S B T Z H C P N =>
      [[BMark.b1, BMark.b0, BMark.b0],
        euclideanAlgorithmEncodeBHist I,
        euclideanAlgorithmEncodeBHist S,
        euclideanAlgorithmEncodeBHist B,
        euclideanAlgorithmEncodeBHist T,
        euclideanAlgorithmEncodeBHist Z,
        euclideanAlgorithmEncodeBHist H,
        euclideanAlgorithmEncodeBHist C,
        euclideanAlgorithmEncodeBHist P,
        euclideanAlgorithmEncodeBHist N]

def euclideanAlgorithmFromEventFlow :
    EventFlow → Option EuclideanAlgorithmUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b1, BMark.b0, BMark.b0], I, S, B, T, Z, H, C, P, N] =>
      some
        (EuclideanAlgorithmUp.mk
          (euclideanAlgorithmDecodeBHist I)
          (euclideanAlgorithmDecodeBHist S)
          (euclideanAlgorithmDecodeBHist B)
          (euclideanAlgorithmDecodeBHist T)
          (euclideanAlgorithmDecodeBHist Z)
          (euclideanAlgorithmDecodeBHist H)
          (euclideanAlgorithmDecodeBHist C)
          (euclideanAlgorithmDecodeBHist P)
          (euclideanAlgorithmDecodeBHist N))
  | _ => none

private theorem euclideanAlgorithm_round_trip :
    ∀ x : EuclideanAlgorithmUp,
      euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S B T Z H C P N =>
      change
        some
          (EuclideanAlgorithmUp.mk
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist I))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist S))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N))) =
          some (EuclideanAlgorithmUp.mk I S B T Z H C P N)
      have hIc :
          EuclideanAlgorithmUp.mk
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist I))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist S))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist S))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun I' =>
            EuclideanAlgorithmUp.mk I'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist S))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist I)
      have hSc :
          EuclideanAlgorithmUp.mk I
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist S))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun S' =>
            EuclideanAlgorithmUp.mk I S'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist S)
      have hBc :
          EuclideanAlgorithmUp.mk I S
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S B
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun B' =>
            EuclideanAlgorithmUp.mk I S B'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist B)
      have hTc :
          EuclideanAlgorithmUp.mk I S B
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S B T
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun T' =>
            EuclideanAlgorithmUp.mk I S B T'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist T)
      have hZc :
          EuclideanAlgorithmUp.mk I S B T
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S B T Z
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun Z' =>
            EuclideanAlgorithmUp.mk I S B T Z'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist Z)
      have hHc :
          EuclideanAlgorithmUp.mk I S B T Z
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S B T Z H
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun H' =>
            EuclideanAlgorithmUp.mk I S B T Z H'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist H)
      have hCc :
          EuclideanAlgorithmUp.mk I S B T Z H
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S B T Z H C
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun C' =>
            EuclideanAlgorithmUp.mk I S B T Z H C'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist C)
      have hPc :
          EuclideanAlgorithmUp.mk I S B T Z H C
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S B T Z H C P
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) :=
        congrArg
          (fun P' =>
            EuclideanAlgorithmUp.mk I S B T Z H C P'
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)))
          (euclideanAlgorithm_decode_encode_bhist P)
      have hNc :
          EuclideanAlgorithmUp.mk I S B T Z H C P
              (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N)) =
            EuclideanAlgorithmUp.mk I S B T Z H C P N :=
        congrArg
          (fun N' => EuclideanAlgorithmUp.mk I S B T Z H C P N')
          (euclideanAlgorithm_decode_encode_bhist N)
      exact congrArg some
        (Eq.trans hIc
          (Eq.trans hSc
            (Eq.trans hBc
              (Eq.trans hTc
                (Eq.trans hZc
                  (Eq.trans hHc (Eq.trans hCc (Eq.trans hPc hNc))))))))

private theorem euclideanAlgorithmToEventFlow_injective
    {x y : EuclideanAlgorithmUp} :
    euclideanAlgorithmToEventFlow x = euclideanAlgorithmToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow x) =
        euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow y) :=
    congrArg euclideanAlgorithmFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (euclideanAlgorithm_round_trip x).symm
      (Eq.trans hread (euclideanAlgorithm_round_trip y)))

private theorem euclideanAlgorithm_field_faithful :
    ∀ x y : EuclideanAlgorithmUp,
      euclideanAlgorithmFields x = euclideanAlgorithmFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 S1 B1 T1 Z1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 S2 B2 T2 Z2 H2 C2 P2 N2 =>
          injection hfields with hI t1
          injection t1 with hS t2
          injection t2 with hB t3
          injection t3 with hT t4
          injection t4 with hZ t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          cases hI
          cases hS
          cases hB
          cases hT
          cases hZ
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance euclideanAlgorithmBHistCarrier :
    BHistCarrier EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := euclideanAlgorithmToEventFlow
  fromEventFlow := euclideanAlgorithmFromEventFlow

instance euclideanAlgorithmChapterTasteGate :
    ChapterTasteGate EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow x) = some x
    exact euclideanAlgorithm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (euclideanAlgorithmToEventFlow_injective heq)

instance euclideanAlgorithmFieldFaithful :
    FieldFaithful EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := euclideanAlgorithmFields
  field_faithful := euclideanAlgorithm_field_faithful

instance euclideanAlgorithmNontrivial :
    Nontrivial EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EuclideanAlgorithmUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EuclideanAlgorithmUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EuclideanAlgorithmUp :=
  -- BEDC touchpoint anchor: BHist BMark
  euclideanAlgorithmChapterTasteGate

theorem EuclideanAlgorithmTasteGate_single_carrier_alignment :
    forall I S B T Z H C P N : BHist,
      euclideanAlgorithmFields (EuclideanAlgorithmUp.mk I S B T Z H C P N) =
        [I, S, B, T, Z, H, C, P, N] ∧
      euclideanAlgorithmToEventFlow (EuclideanAlgorithmUp.mk I S B T Z H C P N) =
        [[BMark.b1, BMark.b0, BMark.b0],
          euclideanAlgorithmEncodeBHist I,
          euclideanAlgorithmEncodeBHist S,
          euclideanAlgorithmEncodeBHist B,
          euclideanAlgorithmEncodeBHist T,
          euclideanAlgorithmEncodeBHist Z,
          euclideanAlgorithmEncodeBHist H,
          euclideanAlgorithmEncodeBHist C,
          euclideanAlgorithmEncodeBHist P,
          euclideanAlgorithmEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  intro I S B T Z H C P N
  exact ⟨rfl, rfl⟩

end BEDC.Derived.EuclideanAlgorithmUp
