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

theorem GroundRefutationCarrier_consumer_readiness {A F H C P N bottom : BHist}
    (carrier : GroundRefutationCarrier A F H C P N) (route : Cont A F bottom) :
    SemanticNameCert
      (fun row : BHist => GroundRefutationCarrier A F H C P N ∧ hsame row bottom)
      (fun row : BHist => Cont A F row ∧ hsame A A)
      (fun row : BHist => hsame row bottom ∧ hsame P N)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro bottom ⟨carrier, hsame_refl bottom⟩
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
        intro row other sameRows sourceRow
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport route (hsame_symm sourceRow.right),
          carrier.right.right.right.left⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨sourceRow.right, carrier.right.right.left⟩
  }

theorem GroundRefutationCarrier_route_stability {A F H C P N routeRead : BHist}
    (carrier : GroundRefutationCarrier A F H C P N)
    (assumptionFalsity : Cont A F routeRead) :
    Cont A F routeRead ∧ Cont A F H ∧ hsame routeRead H ∧ Cont H C P ∧ hsame P N ∧
      hsame A A ∧ hsame F F ∧ hsame C C ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  rcases carrier with
    ⟨storedAssumptionFalsity, continuationProvenance, provenanceName, sameA, sameF, _sameH,
      sameC, sameN⟩
  have routeSameStored : hsame routeRead H :=
    cont_deterministic assumptionFalsity storedAssumptionFalsity
  exact
    ⟨assumptionFalsity, storedAssumptionFalsity, routeSameStored, continuationProvenance,
      provenanceName, sameA, sameF, sameC, sameN⟩

theorem GroundRefutationCarrier_ledger_accountability {A F H C P N bottom : BHist}
    (carrier : GroundRefutationCarrier A F H C P N) (route : Cont A F bottom) :
    SemanticNameCert
        (fun row : BHist => hsame row bottom ∧ GroundRefutationCarrier A F H C P N)
        (fun row : BHist => Cont A F row ∧ Cont H C P)
        (fun row : BHist =>
          hsame row bottom ∧ hsame P N ∧ hsame A A ∧ hsame F F ∧ hsame C C ∧
            hsame N N)
        hsame ∧
      Cont A F bottom ∧ Cont H C P ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  rcases carrier with
    ⟨storedRoute, continuationLedger, provenanceName, sameA, sameF, _sameH, sameC, sameN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bottom ∧ GroundRefutationCarrier A F H C P N)
          (fun row : BHist => Cont A F row ∧ Cont H C P)
          (fun row : BHist =>
            hsame row bottom ∧ hsame P N ∧ hsame A A ∧ hsame F F ∧ hsame C C ∧
              hsame N N)
          hsame := by
    exact {
      core := {
        carrier_inhabited := by
          exact
            Exists.intro bottom
              ⟨hsame_refl bottom,
                ⟨storedRoute, continuationLedger, provenanceName, sameA, sameF,
                  hsame_refl H, sameC, sameN⟩⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨cont_result_hsame_transport route (hsame_symm source.left), continuationLedger⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, provenanceName, sameA, sameF, sameC, sameN⟩
    }
  exact ⟨cert, route, continuationLedger, provenanceName⟩

end BEDC.Derived.GroundRefutationUp
