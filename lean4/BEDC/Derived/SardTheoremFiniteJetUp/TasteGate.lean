import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SardTheoremFiniteJetUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SardTheoremFiniteJetUp : Type where
  | mk (M F D R V L H C P N : BHist) : SardTheoremFiniteJetUp
  deriving DecidableEq

def sardTheoremFiniteJetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sardTheoremFiniteJetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sardTheoremFiniteJetEncodeBHist h

def sardTheoremFiniteJetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sardTheoremFiniteJetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sardTheoremFiniteJetDecodeBHist tail)

private theorem SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      sardTheoremFiniteJetDecodeBHist (sardTheoremFiniteJetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sardTheoremFiniteJetFields : SardTheoremFiniteJetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SardTheoremFiniteJetUp.mk M F D R V L H C P N => [M, F, D, R, V, L, H, C, P, N]

def sardTheoremFiniteJetToEventFlow : SardTheoremFiniteJetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sardTheoremFiniteJetFields x).map sardTheoremFiniteJetEncodeBHist

def sardTheoremFiniteJetFromEventFlow : EventFlow → Option SardTheoremFiniteJetUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: restM =>
      match restM with
      | F :: restF =>
          match restF with
          | D :: restD =>
              match restD with
              | R :: restR =>
                  match restR with
                  | V :: restV =>
                      match restV with
                      | L :: restL =>
                          match restL with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (SardTheoremFiniteJetUp.mk
                                                  (sardTheoremFiniteJetDecodeBHist M)
                                                  (sardTheoremFiniteJetDecodeBHist F)
                                                  (sardTheoremFiniteJetDecodeBHist D)
                                                  (sardTheoremFiniteJetDecodeBHist R)
                                                  (sardTheoremFiniteJetDecodeBHist V)
                                                  (sardTheoremFiniteJetDecodeBHist L)
                                                  (sardTheoremFiniteJetDecodeBHist H)
                                                  (sardTheoremFiniteJetDecodeBHist C)
                                                  (sardTheoremFiniteJetDecodeBHist P)
                                                  (sardTheoremFiniteJetDecodeBHist N))
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

private theorem sardTheoremFiniteJet_mk_congr
    {M M' F F' D D' R R' V V' L L' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hF : F' = F) (hD : D' = D) (hR : R' = R)
    (hV : V' = V) (hL : L' = L) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    SardTheoremFiniteJetUp.mk M' F' D' R' V' L' H' C' P' N' =
      SardTheoremFiniteJetUp.mk M F D R V L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hF
  cases hD
  cases hR
  cases hV
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem SardTheoremFiniteJetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SardTheoremFiniteJetUp,
      sardTheoremFiniteJetFromEventFlow (sardTheoremFiniteJetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F D R V L H C P N =>
      exact
        congrArg some
          (sardTheoremFiniteJet_mk_congr
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode M)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode F)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode D)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode R)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode V)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode L)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode H)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode C)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode P)
            (SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode N))

private theorem sardTheoremFiniteJetToEventFlow_injective {x y : SardTheoremFiniteJetUp} :
    sardTheoremFiniteJetToEventFlow x = sardTheoremFiniteJetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sardTheoremFiniteJetFromEventFlow (sardTheoremFiniteJetToEventFlow x) =
        sardTheoremFiniteJetFromEventFlow (sardTheoremFiniteJetToEventFlow y) :=
    congrArg sardTheoremFiniteJetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SardTheoremFiniteJetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SardTheoremFiniteJetTasteGate_single_carrier_alignment_round_trip y)))

instance sardTheoremFiniteJetBHistCarrier : BHistCarrier SardTheoremFiniteJetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sardTheoremFiniteJetToEventFlow
  fromEventFlow := sardTheoremFiniteJetFromEventFlow

instance sardTheoremFiniteJetChapterTasteGate :
    ChapterTasteGate SardTheoremFiniteJetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sardTheoremFiniteJetFromEventFlow (sardTheoremFiniteJetToEventFlow x) = some x
    exact SardTheoremFiniteJetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sardTheoremFiniteJetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SardTheoremFiniteJetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sardTheoremFiniteJetChapterTasteGate

theorem SardTheoremFiniteJetTasteGate_single_carrier_alignment :
    (∀ h : BHist, sardTheoremFiniteJetDecodeBHist (sardTheoremFiniteJetEncodeBHist h) = h) ∧
      (∀ x : SardTheoremFiniteJetUp,
        sardTheoremFiniteJetFromEventFlow (sardTheoremFiniteJetToEventFlow x) = some x) ∧
        (∀ x y : SardTheoremFiniteJetUp,
          sardTheoremFiniteJetToEventFlow x = sardTheoremFiniteJetToEventFlow y → x = y) ∧
          sardTheoremFiniteJetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SardTheoremFiniteJetTasteGate_single_carrier_alignment_decode,
      SardTheoremFiniteJetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => sardTheoremFiniteJetToEventFlow_injective h),
      rfl⟩

end TasteGate
end BEDC.Derived.SardTheoremFiniteJetUp
