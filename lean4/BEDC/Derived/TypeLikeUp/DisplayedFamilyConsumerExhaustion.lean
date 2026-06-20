import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.TypeLikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TypeLikeDisplayedFamilyConsumerExhaustion [AskSetup] [PackageSetup]
    {B F Q E H C P N endpoint transported replay provenance named setlikeRead firstOrderRead
      modelTheoryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory F -> UnaryHistory Q -> UnaryHistory E ->
      UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
        UnaryHistory setlikeRead -> UnaryHistory firstOrderRead ->
          Cont B F Q -> Cont Q E endpoint -> Cont endpoint H transported ->
            Cont transported C replay -> Cont replay P provenance ->
              Cont provenance N named -> Cont named setlikeRead firstOrderRead ->
                Cont named firstOrderRead modelTheoryRead -> PkgSig bundle P pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row named ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row named ∨ hsame row setlikeRead ∨
                              hsame row firstOrderRead ∨ hsame row modelTheoryRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont B F Q ∧ Cont Q E endpoint ∧
                          Cont endpoint H transported ∧ Cont transported C replay ∧
                            Cont replay P provenance ∧ Cont provenance N named ∧
                              PkgSig bundle P pkg)
                      hsame ∧
                    UnaryHistory endpoint ∧ UnaryHistory transported ∧ UnaryHistory replay ∧
                      UnaryHistory provenance ∧ UnaryHistory named ∧
                        UnaryHistory modelTheoryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro baseUnary fiberUnary classifierUnary exactnessUnary handoffUnary replayUnary
    provenanceUnary nameUnary setlikeUnary firstOrderUnary baseFiberRoute endpointRoute
    transportRoute replayRoute provenanceRoute nameRoute setlikeRoute modelRoute packageRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed classifierUnary exactnessUnary endpointRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed endpointUnary handoffUnary transportRoute
  have replayReadUnary : UnaryHistory replay :=
    unary_cont_closed transportedUnary replayUnary replayRoute
  have provenanceReadUnary : UnaryHistory provenance :=
    unary_cont_closed replayReadUnary provenanceUnary provenanceRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed provenanceReadUnary nameUnary nameRoute
  have firstOrderRouteUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed namedUnary setlikeUnary setlikeRoute
  have modelTheoryUnary : UnaryHistory modelTheoryRead :=
    unary_cont_closed namedUnary firstOrderUnary modelRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row named ∨
                hsame row setlikeRead ∨ hsame row firstOrderRead ∨ hsame row modelTheoryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B F Q ∧ Cont Q E endpoint ∧
              Cont endpoint H transported ∧ Cont transported C replay ∧
                Cont replay P provenance ∧ Cont provenance N named ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baseFiberRoute, endpointRoute, transportRoute, replayRoute,
          provenanceRoute, nameRoute, packageRead⟩
  }
  exact
    ⟨cert, endpointUnary, transportedUnary, replayReadUnary, provenanceReadUnary,
      namedUnary, modelTheoryUnary⟩

theorem TypeLikeSetLikeFirstOrderModelTheoryCarrierBoundary [AskSetup] [PackageSetup]
    {B F Q E H C P N endpoint transported replay provenance named setlikeRead firstOrderRead
      modelTheoryRead carrierBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory F -> UnaryHistory Q -> UnaryHistory E ->
      UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
        UnaryHistory setlikeRead -> UnaryHistory firstOrderRead ->
          Cont B F Q -> Cont Q E endpoint -> Cont endpoint H transported ->
            Cont transported C replay -> Cont replay P provenance ->
              Cont provenance N named -> Cont named setlikeRead firstOrderRead ->
                Cont named firstOrderRead modelTheoryRead ->
                  Cont modelTheoryRead H carrierBoundary -> PkgSig bundle P pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row carrierBoundary ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨
                            hsame row named ∨ hsame row setlikeRead ∨
                              hsame row firstOrderRead ∨ hsame row modelTheoryRead ∨
                                hsame row carrierBoundary)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont B F Q ∧ Cont Q E endpoint ∧
                            Cont endpoint H transported ∧ Cont transported C replay ∧
                              Cont replay P provenance ∧ Cont provenance N named ∧
                                Cont modelTheoryRead H carrierBoundary ∧ PkgSig bundle P pkg)
                        hsame ∧
                      UnaryHistory endpoint ∧ UnaryHistory transported ∧ UnaryHistory replay ∧
                        UnaryHistory provenance ∧ UnaryHistory named ∧
                          UnaryHistory modelTheoryRead ∧ UnaryHistory carrierBoundary := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro baseUnary fiberUnary classifierUnary exactnessUnary handoffUnary replayUnary
    provenanceUnary nameUnary setlikeUnary firstOrderUnary baseFiberRoute endpointRoute
    transportRoute replayRoute provenanceRoute nameRoute setlikeRoute modelRoute
    carrierBoundaryRoute packageRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed classifierUnary exactnessUnary endpointRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed endpointUnary handoffUnary transportRoute
  have replayReadUnary : UnaryHistory replay :=
    unary_cont_closed transportedUnary replayUnary replayRoute
  have provenanceReadUnary : UnaryHistory provenance :=
    unary_cont_closed replayReadUnary provenanceUnary provenanceRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed provenanceReadUnary nameUnary nameRoute
  have firstOrderRouteUnary : UnaryHistory firstOrderRead :=
    unary_cont_closed namedUnary setlikeUnary setlikeRoute
  have modelTheoryUnary : UnaryHistory modelTheoryRead :=
    unary_cont_closed namedUnary firstOrderUnary modelRoute
  have carrierBoundaryUnary : UnaryHistory carrierBoundary :=
    unary_cont_closed modelTheoryUnary handoffUnary carrierBoundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row carrierBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨ hsame row named ∨
              hsame row setlikeRead ∨ hsame row firstOrderRead ∨ hsame row modelTheoryRead ∨
                hsame row carrierBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B F Q ∧ Cont Q E endpoint ∧
              Cont endpoint H transported ∧ Cont transported C replay ∧
                Cont replay P provenance ∧ Cont provenance N named ∧
                  Cont modelTheoryRead H carrierBoundary ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro carrierBoundary ⟨hsame_refl carrierBoundary, carrierBoundaryUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baseFiberRoute, endpointRoute, transportRoute, replayRoute,
          provenanceRoute, nameRoute, carrierBoundaryRoute, packageRead⟩
  }
  exact
    ⟨cert, endpointUnary, transportedUnary, replayReadUnary, provenanceReadUnary,
      namedUnary, modelTheoryUnary, carrierBoundaryUnary⟩

theorem TypeLikeDisplayedFamilyInversion [AskSetup] [PackageSetup]
    {B F Q E H C P N endpoint transported replay provenance named familyRead
      inversionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory F -> UnaryHistory Q -> UnaryHistory E ->
      UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
        Cont B F Q -> Cont Q E endpoint -> Cont endpoint H transported ->
          Cont transported C replay -> Cont replay P provenance ->
            Cont provenance N named -> Cont named F familyRead ->
              Cont familyRead E inversionRead -> PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row inversionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨
                        hsame row named ∨ hsame row familyRead ∨ hsame row inversionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont provenance N named ∧
                        Cont named F familyRead ∧ Cont familyRead E inversionRead ∧
                          PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory endpoint ∧ UnaryHistory transported ∧ UnaryHistory replay ∧
                    UnaryHistory provenance ∧ UnaryHistory named ∧ UnaryHistory familyRead ∧
                      UnaryHistory inversionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro baseUnary fiberUnary classifierUnary exactnessUnary handoffUnary replayUnary
    provenanceUnary nameUnary _baseFiberRoute endpointRoute transportRoute replayRoute
    provenanceRoute nameRoute familyRoute inversionRoute packageRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed classifierUnary exactnessUnary endpointRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed endpointUnary handoffUnary transportRoute
  have replayReadUnary : UnaryHistory replay :=
    unary_cont_closed transportedUnary replayUnary replayRoute
  have provenanceReadUnary : UnaryHistory provenance :=
    unary_cont_closed replayReadUnary provenanceUnary provenanceRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed provenanceReadUnary nameUnary nameRoute
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed namedUnary fiberUnary familyRoute
  have inversionUnary : UnaryHistory inversionRead :=
    unary_cont_closed familyUnary exactnessUnary inversionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row inversionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row F ∨ hsame row Q ∨ hsame row E ∨ hsame row named ∨
              hsame row familyRead ∨ hsame row inversionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont provenance N named ∧ Cont named F familyRead ∧
              Cont familyRead E inversionRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro inversionRead ⟨hsame_refl inversionRead, inversionUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nameRoute, familyRoute, inversionRoute, packageRead⟩
  }
  exact
    ⟨cert, endpointUnary, transportedUnary, replayReadUnary, provenanceReadUnary, namedUnary,
      familyUnary, inversionUnary⟩

end BEDC.Derived.TypeLikeUp
