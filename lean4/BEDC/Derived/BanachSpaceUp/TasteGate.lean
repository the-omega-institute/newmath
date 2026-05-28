import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachSpaceUp : Type where
  | mk (V N M Q S R E Z H C P L : BHist) : BanachSpaceUp
  deriving DecidableEq

def banachSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachSpaceEncodeBHist h

def banachSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachSpaceDecodeBHist tail)

private theorem banachSpace_decode_encode :
    ∀ h : BHist, banachSpaceDecodeBHist (banachSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachSpaceFields : BanachSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachSpaceUp.mk V N M Q S R E Z H C P L => [V, N, M, Q, S, R, E, Z, H, C, P, L]

def banachSpaceToEventFlow : BanachSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (banachSpaceFields token).map banachSpaceEncodeBHist

def banachSpaceFromEventFlow : EventFlow → Option BanachSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | V :: restV =>
      match restV with
      | N :: restN =>
          match restN with
          | M :: restM =>
              match restM with
              | Q :: restQ =>
                  match restQ with
                  | S :: restS =>
                      match restS with
                      | R :: restR =>
                          match restR with
                          | E :: restE =>
                              match restE with
                              | Z :: restZ =>
                                  match restZ with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | L :: restL =>
                                                  match restL with
                                                  | [] =>
                                                      some
                                                        (BanachSpaceUp.mk
                                                          (banachSpaceDecodeBHist V)
                                                          (banachSpaceDecodeBHist N)
                                                          (banachSpaceDecodeBHist M)
                                                          (banachSpaceDecodeBHist Q)
                                                          (banachSpaceDecodeBHist S)
                                                          (banachSpaceDecodeBHist R)
                                                          (banachSpaceDecodeBHist E)
                                                          (banachSpaceDecodeBHist Z)
                                                          (banachSpaceDecodeBHist H)
                                                          (banachSpaceDecodeBHist C)
                                                          (banachSpaceDecodeBHist P)
                                                          (banachSpaceDecodeBHist L))
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

private theorem banachSpace_round_trip :
    ∀ token : BanachSpaceUp,
      banachSpaceFromEventFlow (banachSpaceToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk V N M Q S R E Z H C P L =>
      change
        some
            (BanachSpaceUp.mk
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist V))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist N))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist M))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist Q))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist S))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist R))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist E))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist Z))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist H))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist C))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist P))
              (banachSpaceDecodeBHist (banachSpaceEncodeBHist L))) =
          some (BanachSpaceUp.mk V N M Q S R E Z H C P L)
      rw [banachSpace_decode_encode V]
      rw [banachSpace_decode_encode N]
      rw [banachSpace_decode_encode M]
      rw [banachSpace_decode_encode Q]
      rw [banachSpace_decode_encode S]
      rw [banachSpace_decode_encode R]
      rw [banachSpace_decode_encode E]
      rw [banachSpace_decode_encode Z]
      rw [banachSpace_decode_encode H]
      rw [banachSpace_decode_encode C]
      rw [banachSpace_decode_encode P]
      rw [banachSpace_decode_encode L]

private theorem banachSpaceToEventFlow_injective {x y : BanachSpaceUp} :
    banachSpaceToEventFlow x = banachSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachSpaceFromEventFlow (banachSpaceToEventFlow x) =
        banachSpaceFromEventFlow (banachSpaceToEventFlow y) :=
    congrArg banachSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (banachSpace_round_trip x).symm
      (Eq.trans hread (banachSpace_round_trip y)))

instance banachSpaceBHistCarrier : BHistCarrier BanachSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachSpaceToEventFlow
  fromEventFlow := banachSpaceFromEventFlow

instance banachSpaceChapterTasteGate : ChapterTasteGate BanachSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachSpaceFromEventFlow (banachSpaceToEventFlow x) = some x
    exact banachSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (banachSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BanachSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachSpaceChapterTasteGate

theorem BanachSpaceTasteGate_single_carrier_alignment :
    ChapterTasteGate BanachSpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact banachSpaceChapterTasteGate

end BEDC.Derived.BanachSpaceUp
