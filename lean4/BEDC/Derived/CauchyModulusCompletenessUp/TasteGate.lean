import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusCompletenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusCompletenessUp : Type where
  | mk (M E K W R D L H C P N : BHist) : CauchyModulusCompletenessUp
  deriving DecidableEq

def cauchyModulusCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusCompletenessEncodeBHist h

def cauchyModulusCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusCompletenessDecodeBHist tail)

private theorem cauchyModulusCompletenessDecode_encode :
    ∀ h : BHist,
      cauchyModulusCompletenessDecodeBHist
          (cauchyModulusCompletenessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusCompletenessFields :
    CauchyModulusCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusCompletenessUp.mk M E K W R D L H C P N =>
      [M, E, K, W, R, D, L, H, C, P, N]

def cauchyModulusCompletenessToEventFlow :
    CauchyModulusCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyModulusCompletenessFields x).map
        cauchyModulusCompletenessEncodeBHist

def cauchyModulusCompletenessFromEventFlow :
    EventFlow → Option CauchyModulusCompletenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | E :: restE =>
          match restE with
          | K :: restK =>
              match restK with
              | W :: restW =>
                  match restW with
                  | R :: restR =>
                      match restR with
                      | D :: restD =>
                          match restD with
                          | L :: restL =>
                              match restL with
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
                                                    (CauchyModulusCompletenessUp.mk
                                                      (cauchyModulusCompletenessDecodeBHist M)
                                                      (cauchyModulusCompletenessDecodeBHist E)
                                                      (cauchyModulusCompletenessDecodeBHist K)
                                                      (cauchyModulusCompletenessDecodeBHist W)
                                                      (cauchyModulusCompletenessDecodeBHist R)
                                                      (cauchyModulusCompletenessDecodeBHist D)
                                                      (cauchyModulusCompletenessDecodeBHist L)
                                                      (cauchyModulusCompletenessDecodeBHist H)
                                                      (cauchyModulusCompletenessDecodeBHist C)
                                                      (cauchyModulusCompletenessDecodeBHist P)
                                                      (cauchyModulusCompletenessDecodeBHist N))
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

private theorem cauchyModulusCompleteness_mk_congr
    {M M' E E' K K' W W' R R' D D' L L' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hE : E' = E) (hK : K' = K) (hW : W' = W)
    (hR : R' = R) (hD : D' = D) (hL : L' = L) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyModulusCompletenessUp.mk M' E' K' W' R' D' L' H' C' P' N' =
      CauchyModulusCompletenessUp.mk M E K W R D L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hE
  cases hK
  cases hW
  cases hR
  cases hD
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem cauchyModulusCompleteness_round_trip :
    ∀ x : CauchyModulusCompletenessUp,
      cauchyModulusCompletenessFromEventFlow
          (cauchyModulusCompletenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E K W R D L H C P N =>
      exact
        congrArg some
          (cauchyModulusCompleteness_mk_congr
            (cauchyModulusCompletenessDecode_encode M)
            (cauchyModulusCompletenessDecode_encode E)
            (cauchyModulusCompletenessDecode_encode K)
            (cauchyModulusCompletenessDecode_encode W)
            (cauchyModulusCompletenessDecode_encode R)
            (cauchyModulusCompletenessDecode_encode D)
            (cauchyModulusCompletenessDecode_encode L)
            (cauchyModulusCompletenessDecode_encode H)
            (cauchyModulusCompletenessDecode_encode C)
            (cauchyModulusCompletenessDecode_encode P)
            (cauchyModulusCompletenessDecode_encode N))

private theorem cauchyModulusCompletenessToEventFlow_injective
    {x y : CauchyModulusCompletenessUp} :
    cauchyModulusCompletenessToEventFlow x =
      cauchyModulusCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusCompletenessFromEventFlow
          (cauchyModulusCompletenessToEventFlow x) =
        cauchyModulusCompletenessFromEventFlow
          (cauchyModulusCompletenessToEventFlow y) :=
    congrArg cauchyModulusCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusCompleteness_round_trip x).symm
      (Eq.trans hread (cauchyModulusCompleteness_round_trip y)))

instance cauchyModulusCompletenessBHistCarrier :
    BHistCarrier CauchyModulusCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusCompletenessToEventFlow
  fromEventFlow := cauchyModulusCompletenessFromEventFlow

instance cauchyModulusCompletenessChapterTasteGate :
    ChapterTasteGate CauchyModulusCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusCompletenessFromEventFlow
          (cauchyModulusCompletenessToEventFlow x) = some x
    exact cauchyModulusCompleteness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusCompletenessToEventFlow_injective heq)

theorem CauchyModulusCompletenessTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyModulusCompletenessUp) ∧
      Nonempty (ChapterTasteGate CauchyModulusCompletenessUp) ∧
      (∀ h : BHist,
        cauchyModulusCompletenessDecodeBHist
            (cauchyModulusCompletenessEncodeBHist h) =
          h) ∧
      (∀ x : CauchyModulusCompletenessUp,
        cauchyModulusCompletenessFromEventFlow
            (cauchyModulusCompletenessToEventFlow x) =
          some x) ∧
      cauchyModulusCompletenessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyModulusCompletenessBHistCarrier⟩,
      ⟨cauchyModulusCompletenessChapterTasteGate⟩,
      cauchyModulusCompletenessDecode_encode,
      cauchyModulusCompleteness_round_trip,
      rfl⟩

end BEDC.Derived.CauchyModulusCompletenessUp.TasteGate
