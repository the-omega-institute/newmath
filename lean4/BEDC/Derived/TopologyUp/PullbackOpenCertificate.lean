import BEDC.Derived.TopologyUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem BHistPullbackOpen_semantic_name_certificate (T : BHistIndexedOpenCarrier)
    {f : BHist -> BHist} {i : T.OpenIx} {U : BHist -> Prop}
    (mapUnary : forall {y : BHist}, UnaryHistory y -> UnaryHistory (f y))
    (mapSame :
      forall {y z : BHist}, UnaryHistory y -> UnaryHistory z -> hsame y z ->
        hsame (f y) (f z))
    (carryU : BHistCarriesOpen T i U)
    (source : exists y : BHist, UnaryHistory y ∧ BHistPullbackOpen f U y) :
    SemanticNameCert (fun y : BHist => UnaryHistory y ∧ BHistPullbackOpen f U y)
      (fun y : BHist => T.OpenAt i (f y))
      (fun y : BHist => T.OpenAt i (f y))
      (fun y z : BHist => UnaryHistory y ∧ UnaryHistory z ∧ hsame y z) := by
  exact {
    core := {
      carrier_inhabited := source
      equiv_refl := by
        intro y sourceY
        exact And.intro sourceY.left
          (And.intro sourceY.left (hsame_refl y))
      equiv_symm := by
        intro y z classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro y z w classifiedYZ classifiedZW
        exact And.intro classifiedYZ.left
          (And.intro classifiedZW.right.left
            (hsame_trans classifiedYZ.right.right classifiedZW.right.right))
      carrier_respects_equiv := by
        intro y z classified sourceY
        have unaryFY : UnaryHistory (f y) := mapUnary sourceY.left
        have unaryFZ : UnaryHistory (f z) := mapUnary classified.right.left
        have sameF : hsame (f y) (f z) :=
          mapSame sourceY.left classified.right.left classified.right.right
        have carryY : U (f y) <-> T.OpenAt i (f y) := carryU unaryFY
        have carryZ : U (f z) <-> T.OpenAt i (f z) := carryU unaryFZ
        have stable : T.OpenAt i (f y) <-> T.OpenAt i (f z) :=
          T.membership_stable unaryFY unaryFZ sameF
        have openY : T.OpenAt i (f y) := Iff.mp carryY sourceY.right
        have openZ : T.OpenAt i (f z) := Iff.mp stable openY
        exact And.intro classified.right.left (Iff.mpr carryZ openZ)
    }
    pattern_sound := by
      intro y sourceY
      have unaryFY : UnaryHistory (f y) := mapUnary sourceY.left
      have carryY : U (f y) <-> T.OpenAt i (f y) := carryU unaryFY
      exact Iff.mp carryY sourceY.right
    ledger_sound := by
      intro y sourceY
      have unaryFY : UnaryHistory (f y) := mapUnary sourceY.left
      have carryY : U (f y) <-> T.OpenAt i (f y) := carryU unaryFY
      exact Iff.mp carryY sourceY.right
  }

end BEDC.Derived.TopologyUp
