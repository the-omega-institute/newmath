import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BranchObstructionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BranchObstructionUp : Type where
  | mk :
      (source branch history classifier package name : BHist) →
      BranchObstructionUp
  deriving DecidableEq

private def branchObstructionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: branchObstructionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: branchObstructionEncodeBHist h

private def branchObstructionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (branchObstructionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (branchObstructionDecodeBHist tail)

private theorem branchObstructionDecodeEncodeBHist :
    ∀ h : BHist, branchObstructionDecodeBHist (branchObstructionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem branchObstructionMkCongr
    {source source' branch branch' history history' classifier classifier' package package'
      name name' : BHist} :
    source = source' →
      branch = branch' →
        history = history' →
          classifier = classifier' →
            package = package' →
              name = name' →
                BranchObstructionUp.mk source branch history classifier package name =
                  BranchObstructionUp.mk source' branch' history' classifier' package' name' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hsource hbranch hhistory hclassifier hpackage hname
  cases hsource
  cases hbranch
  cases hhistory
  cases hclassifier
  cases hpackage
  cases hname
  rfl

private def branchObstructionToEventFlow : BranchObstructionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BranchObstructionUp.mk source branch history classifier package name =>
      [branchObstructionEncodeBHist source,
        branchObstructionEncodeBHist branch,
        branchObstructionEncodeBHist history,
        branchObstructionEncodeBHist classifier,
        branchObstructionEncodeBHist package,
        branchObstructionEncodeBHist name]

private def branchObstructionFromEventFlow : EventFlow → Option BranchObstructionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | branch :: rest1 =>
          match rest1 with
          | [] => none
          | history :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | package :: rest4 =>
                      match rest4 with
                      | [] => none
                      | name :: rest5 =>
                          match rest5 with
                          | [] =>
                              some
                                (BranchObstructionUp.mk
                                  (branchObstructionDecodeBHist source)
                                  (branchObstructionDecodeBHist branch)
                                  (branchObstructionDecodeBHist history)
                                  (branchObstructionDecodeBHist classifier)
                                  (branchObstructionDecodeBHist package)
                                  (branchObstructionDecodeBHist name))
                          | _ :: _ => none

private theorem branchObstruction_round_trip :
    ∀ x : BranchObstructionUp,
      branchObstructionFromEventFlow (branchObstructionToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | BranchObstructionUp.mk source branch history classifier package name =>
      congrArg some
        (branchObstructionMkCongr
          (branchObstructionDecodeEncodeBHist source)
          (branchObstructionDecodeEncodeBHist branch)
          (branchObstructionDecodeEncodeBHist history)
          (branchObstructionDecodeEncodeBHist classifier)
          (branchObstructionDecodeEncodeBHist package)
          (branchObstructionDecodeEncodeBHist name))

private theorem branchObstructionToEventFlow_injective {x y : BranchObstructionUp} :
    branchObstructionToEventFlow x = branchObstructionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      branchObstructionFromEventFlow (branchObstructionToEventFlow x) =
        branchObstructionFromEventFlow (branchObstructionToEventFlow y) :=
    congrArg branchObstructionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (branchObstruction_round_trip x).symm
      (Eq.trans hread (branchObstruction_round_trip y)))

instance branchObstructionBHistCarrier : BHistCarrier BranchObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := branchObstructionToEventFlow
  fromEventFlow := branchObstructionFromEventFlow

instance branchObstructionChapterTasteGate : ChapterTasteGate BranchObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change branchObstructionFromEventFlow (branchObstructionToEventFlow x) = some x
    exact branchObstruction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (branchObstructionToEventFlow_injective heq)

theorem BranchObstructionTasteGate_single_carrier_alignment :
    (∀ x : BranchObstructionUp,
      branchObstructionFromEventFlow (branchObstructionToEventFlow x) = some x) ∧
      (∀ x y : BranchObstructionUp,
        branchObstructionToEventFlow x = branchObstructionToEventFlow y → x = y) ∧
        ∃ x : BranchObstructionUp,
          x =
              BranchObstructionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty ∧
            branchObstructionFromEventFlow (branchObstructionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  let x : BranchObstructionUp :=
    BranchObstructionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  constructor
  · exact branchObstruction_round_trip
  · constructor
    · intro left right heq
      exact branchObstructionToEventFlow_injective heq
    · exact ⟨x, rfl, branchObstruction_round_trip x⟩

end BEDC.Derived.BranchObstructionUp
