import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert

namespace BEDC.Derived.GroundRefutationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert

def GroundRefutationCarrier (A F H C P N : BHist) : Prop :=
  Cont A F H ∧ Cont H C P ∧ hsame P N ∧ hsame A A ∧ hsame F F ∧
    hsame H H ∧ hsame C C ∧ hsame N N

theorem GroundRefutationNameCertObligations
    {A F H C P N bottom : BHist}
    (carrier : GroundRefutationCarrier A F H C P N)
    (route : Cont A F bottom) :
    Cont A F bottom ∧ hsame A A ∧ hsame F F ∧ hsame H H ∧ hsame C C ∧
      hsame P P ∧ hsame N N ∧ msame BMark.b0 BMark.b0 := by
  -- BEDC touchpoint anchor: BHist Cont hsame msame BMark
  exact
    ⟨route, carrier.right.right.right.left, carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left, rfl,
      carrier.right.right.right.right.right.right.right, rfl⟩

theorem GroundRefutationCarrier_ground_loop_boundary {A F H C P N : BHist}
    (carrier : GroundRefutationCarrier A F H C P N) :
    Cont A (append F C) P ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  constructor
  · cases carrier with
    | intro first rest =>
        cases rest with
        | intro second rest =>
            cases first
            cases second
            exact append_assoc A F C
  · exact carrier.right.right.left

theorem GroundRefutationCarrier_classifier_transport
    {A F H C P N A' F' H' C' P' N' transported : BHist}
    (carrier : GroundRefutationCarrier A F H C P N)
    (sameA : hsame A A')
    (sameF : hsame F F')
    (sameH : hsame H H')
    (sameC : hsame C C')
    (sameP : hsame P P')
    (sameN : hsame N N')
    (transportedRoute : Cont A' F' transported)
    (sameTransported : hsame transported H') :
    hsame transported H' ∧ hsame P' N' ∧
      GroundRefutationCarrier A' F' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases sameA
  cases sameF
  cases sameH
  cases sameC
  cases sameP
  cases sameN
  constructor
  · exact sameTransported
  · constructor
    · exact carrier.right.right.left
    · exact
        ⟨cont_result_hsame_transport transportedRoute sameTransported,
          carrier.right.left,
          carrier.right.right.left,
          carrier.right.right.right.left,
          carrier.right.right.right.right.left,
          carrier.right.right.right.right.right.left,
          carrier.right.right.right.right.right.right.left,
          carrier.right.right.right.right.right.right.right⟩

theorem GroundRefutationCarrier_route_semantic_name_certificate
    {A F H C P N bottom returned : BHist}
    (carrier : GroundRefutationCarrier A F H C P N)
    (route : Cont A F bottom)
    (returnRoute : Cont bottom C returned) :
    SemanticNameCert
      (fun row : BHist => hsame row returned ∧ GroundRefutationCarrier A F H C P N)
      (fun row : BHist => Cont A F bottom ∧ Cont bottom C row ∧ hsame P N)
      (fun row : BHist => Cont A (append F C) P ∧ Cont bottom C row ∧ hsame A A ∧ hsame F F)
      (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont hsame append SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro returned ⟨rfl, carrier⟩
      equiv_refl := by
        intro row source
        rfl
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact source.right
    }
    pattern_sound := by
      intro row source
      constructor
      · exact route
      · constructor
        · cases source.left
          exact returnRoute
        · exact carrier.right.right.left
    ledger_sound := by
      intro row source
      constructor
      · exact (GroundRefutationCarrier_ground_loop_boundary carrier).left
      · constructor
        · cases source.left
          exact returnRoute
        · constructor
          · exact carrier.right.right.right.left
          · exact carrier.right.right.right.right.left
  }

theorem GroundRefutationCarrier_consumer_readiness_certificate
    {A F H C P N bottom consumer : BHist}
    (carrier : GroundRefutationCarrier A F H C P N)
    (route : Cont A F bottom)
    (consume : Cont bottom P consumer) :
    SemanticNameCert
      (fun row : BHist => hsame row consumer ∧ GroundRefutationCarrier A F H C P N)
      (fun row : BHist => Cont A F bottom ∧ Cont bottom P row ∧ hsame P N)
      (fun row : BHist => Cont A (append F C) P ∧ Cont bottom P row ∧ hsame N N)
      (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont hsame append SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨rfl, carrier⟩
      equiv_refl := by
        intro row source
        rfl
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact source.right
    }
    pattern_sound := by
      intro row source
      constructor
      · exact route
      · constructor
        · cases source.left
          exact consume
        · exact carrier.right.right.left
    ledger_sound := by
      intro row source
      constructor
      · exact (GroundRefutationCarrier_ground_loop_boundary carrier).left
      · constructor
        · cases source.left
          exact consume
        · exact carrier.right.right.right.right.right.right.right
  }

end BEDC.Derived.GroundRefutationUp
