import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Assoc
import BEDC.FKernel.NameCert

namespace BEDC.Derived.GroundLoopBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def GroundLoopBoundaryCarrier (M S X R H C P N : BHist) : Prop :=
  msame BMark.b0 BMark.b0 ∧ msame BMark.b1 BMark.b1 ∧ Cont M S X ∧ Cont X R C ∧
    hsame P N ∧ hsame H H ∧ hsame N N

theorem GroundLoopBoundaryCarrier_ground_replay_composite
    {M S X R H C P N : BHist}
    (carrier : GroundLoopBoundaryCarrier M S X R H C P N) :
    Cont M (append S R) C ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · cases carrier.right.right.left
    cases carrier.right.right.right.left
    exact append_assoc M S R
  · exact carrier.right.right.right.right.left

theorem GroundLoopBoundaryCarrier_scoped_kernel_route
    {M S X R H C P N : BHist}
    (carrier : GroundLoopBoundaryCarrier M S X R H C P N) :
    msame BMark.b0 BMark.b0 ∧ msame BMark.b1 BMark.b1 ∧
      Cont M (append S R) C ∧ hsame P N ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame msame
  have replay := GroundLoopBoundaryCarrier_ground_replay_composite carrier
  exact
    ⟨carrier.left, carrier.right.left, replay.left, replay.right,
      carrier.right.right.right.right.right.right⟩

theorem GroundLoopBoundaryCarrier_public_interface
    {M S X R H C P N : BHist}
    (carrier : GroundLoopBoundaryCarrier M S X R H C P N) :
    SemanticNameCert
      (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
      (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
      (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
      hsame ∧ msame BMark.b0 BMark.b0 ∧ msame BMark.b1 BMark.b1 ∧
        Cont M (append S R) C ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame SemanticNameCert NameCert
  have replay := GroundLoopBoundaryCarrier_ground_replay_composite carrier
  have sourceN :
      (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N) N := by
    exact ⟨carrier, hsame_refl N⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
        (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
        (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceN
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
          exact ⟨carrier, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨cert, carrier.left, carrier.right.left, replay.left, replay.right⟩

theorem GroundLoopBoundaryCarrier_namecert_obligations
    {M S X R H C P N : BHist}
    (carrier : GroundLoopBoundaryCarrier M S X R H C P N) :
    SemanticNameCert
        (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
        (fun row : BHist =>
          msame BMark.b0 BMark.b0 ∧ msame BMark.b1 BMark.b1 ∧ Cont M S X ∧
            Cont X R C ∧ hsame row N)
        (fun row : BHist => hsame row N ∧ hsame P N ∧ hsame H H)
        hsame ∧
      Cont M S X ∧ Cont X R C ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame msame SemanticNameCert
  have sourceN :
      (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N) N := by
    exact ⟨carrier, hsame_refl N⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => GroundLoopBoundaryCarrier M S X R H C P N ∧ hsame row N)
        (fun row : BHist =>
          msame BMark.b0 BMark.b0 ∧ msame BMark.b1 BMark.b1 ∧ Cont M S X ∧
            Cont X R C ∧ hsame row N)
        (fun row : BHist => hsame row N ∧ hsame P N ∧ hsame H H)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceN
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
          exact ⟨carrier, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨carrier.left, carrier.right.left, carrier.right.right.left,
            carrier.right.right.right.left, source.right⟩
      ledger_sound := by
        intro row source
        exact
          ⟨source.right, carrier.right.right.right.right.left,
            carrier.right.right.right.right.right.left⟩
    }
  exact
    ⟨cert, carrier.right.right.left, carrier.right.right.right.left,
      carrier.right.right.right.right.left⟩

theorem GroundLoopBoundaryCarrier_mature_consumer_exhaustion
    {M S X R H C P N L B consumer : BHist}
    (carrier : GroundLoopBoundaryCarrier M S X R H C P N)
    (sibling : Cont R L B)
    (extended : Cont C L consumer) :
    Cont M (append S B) consumer ∧ hsame P N ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · cases carrier.right.right.left
    cases carrier.right.right.right.left
    cases sibling
    cases extended
    exact (append_assoc (append M S) R L).trans (append_assoc M S (append R L))
  · constructor
    · exact carrier.right.right.right.right.left
    · exact carrier.right.right.right.right.right.right

end BEDC.Derived.GroundLoopBoundaryUp
