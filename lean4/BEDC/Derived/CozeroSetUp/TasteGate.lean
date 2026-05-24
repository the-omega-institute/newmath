import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CozeroSetUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CozeroSetUp : Type where
  | mk (F R A O S H K P N : BHist) : CozeroSetUp
  deriving DecidableEq

def cozeroSetEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cozeroSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cozeroSetEncodeBHist h

def cozeroSetDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cozeroSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cozeroSetDecodeBHist tail)

private theorem CozeroSetUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cozeroSetDecodeBHist (cozeroSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cozeroSetFields : CozeroSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CozeroSetUp.mk F R A O S H K P N => [F, R, A, O, S, H, K, P, N]

def cozeroSetToEventFlow : CozeroSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cozeroSetFields x).map cozeroSetEncodeBHist

def cozeroSetFromEventFlow : EventFlow → Option CozeroSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | R :: restR =>
          match restR with
          | A :: restA =>
              match restA with
              | O :: restO =>
                  match restO with
                  | S :: restS =>
                      match restS with
                      | H :: restH =>
                          match restH with
                          | K :: restK =>
                              match restK with
                              | P :: restP =>
                                  match restP with
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (CozeroSetUp.mk
                                              (cozeroSetDecodeBHist F)
                                              (cozeroSetDecodeBHist R)
                                              (cozeroSetDecodeBHist A)
                                              (cozeroSetDecodeBHist O)
                                              (cozeroSetDecodeBHist S)
                                              (cozeroSetDecodeBHist H)
                                              (cozeroSetDecodeBHist K)
                                              (cozeroSetDecodeBHist P)
                                              (cozeroSetDecodeBHist N))
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

private theorem cozeroSet_mk_congr
    {F F' R R' A A' O O' S S' H H' K K' P P' N N' : BHist}
    (hF : F' = F) (hR : R' = R) (hA : A' = A) (hO : O' = O)
    (hS : S' = S) (hH : H' = H) (hK : K' = K) (hP : P' = P)
    (hN : N' = N) :
    CozeroSetUp.mk F' R' A' O' S' H' K' P' N' =
      CozeroSetUp.mk F R A O S H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hR
  cases hA
  cases hO
  cases hS
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

private theorem CozeroSetUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CozeroSetUp, cozeroSetFromEventFlow (cozeroSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F R A O S H K P N =>
      exact
        congrArg some
          (cozeroSet_mk_congr
            (CozeroSetUpTasteGate_single_carrier_alignment_decode F)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode R)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode A)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode O)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode S)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode H)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode K)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode P)
            (CozeroSetUpTasteGate_single_carrier_alignment_decode N))

private theorem cozeroSetToEventFlow_injective {x y : CozeroSetUp} :
    cozeroSetToEventFlow x = cozeroSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cozeroSetFromEventFlow (cozeroSetToEventFlow x) =
        cozeroSetFromEventFlow (cozeroSetToEventFlow y) :=
    congrArg cozeroSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CozeroSetUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CozeroSetUpTasteGate_single_carrier_alignment_round_trip y)))

instance cozeroSetBHistCarrier : BHistCarrier CozeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cozeroSetToEventFlow
  fromEventFlow := cozeroSetFromEventFlow

instance cozeroSetChapterTasteGate : ChapterTasteGate CozeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cozeroSetFromEventFlow (cozeroSetToEventFlow x) = some x
    exact CozeroSetUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cozeroSetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CozeroSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cozeroSetChapterTasteGate

theorem CozeroSetUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cozeroSetDecodeBHist (cozeroSetEncodeBHist h) = h) ∧
      (∀ x : CozeroSetUp, cozeroSetFromEventFlow (cozeroSetToEventFlow x) = some x) ∧
      (∀ x y : CozeroSetUp, cozeroSetToEventFlow x = cozeroSetToEventFlow y → x = y) ∧
      cozeroSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CozeroSetUpTasteGate_single_carrier_alignment_decode
  constructor
  · exact CozeroSetUpTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cozeroSetToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.CozeroSetUp
