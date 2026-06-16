import BEDC.Derived.MetricEmbeddingUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.Derived.MetricEmbeddingUp.TasteGate
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

namespace GraphDistanceControl

theorem MetricEmbeddingGraphDistance_control
    {X F Y R sourceGraph targetGraph comparisonRead : BHist}
    (unaryX : UnaryHistory X)
    (unaryF : UnaryHistory F)
    (unaryY : UnaryHistory Y)
    (unaryR : UnaryHistory R)
    (sourceRoute : Cont X F sourceGraph)
    (targetRoute : Cont sourceGraph Y targetGraph)
    (comparisonRoute : Cont targetGraph R comparisonRead) :
    UnaryHistory sourceGraph ∧ UnaryHistory targetGraph ∧ UnaryHistory comparisonRead ∧
      Cont X F sourceGraph ∧ Cont sourceGraph Y targetGraph ∧
        Cont targetGraph R comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  have unarySourceGraph : UnaryHistory sourceGraph :=
    unary_cont_closed unaryX unaryF sourceRoute
  have unaryTargetGraph : UnaryHistory targetGraph :=
    unary_cont_closed unarySourceGraph unaryY targetRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryTargetGraph unaryR comparisonRoute
  exact
    ⟨unarySourceGraph, unaryTargetGraph, unaryComparisonRead,
      sourceRoute, targetRoute, comparisonRoute⟩

end GraphDistanceControl

theorem MetricEmbeddingGraphDistanceControl [AskSetup] [PackageSetup]
    {X Y F D R S H C P N sourceRead graphRead targetRead controlRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory Y ->
        UnaryHistory F ->
          UnaryHistory D ->
            UnaryHistory R ->
              UnaryHistory S ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont X F sourceRead ->
                          Cont sourceRead Y graphRead ->
                            Cont graphRead D targetRead ->
                              Cont targetRead R controlRead ->
                                Cont controlRead S sealRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row sealRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row Y ∨ hsame row F ∨
                                              hsame row D ∨ hsame row R ∨ hsame row S ∨
                                                hsame row sealRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                              PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory sourceRead ∧ UnaryHistory graphRead ∧
                                          UnaryHistory targetRead ∧
                                            UnaryHistory controlRead ∧
                                              UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro xUnary yUnary fUnary dUnary rUnary sUnary _hUnary _cUnary _pUnary _nUnary
    sourceRoute graphRoute targetRoute controlRoute sealRoute provenancePkg namePkg
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary fUnary sourceRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed sourceReadUnary yUnary graphRoute
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed graphReadUnary dUnary targetRoute
  have controlReadUnary : UnaryHistory controlRead :=
    unary_cont_closed targetReadUnary rUnary controlRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed controlReadUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row F ∨ hsame row D ∨ hsame row R ∨
              hsame row S ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg⟩
    }
  exact
    ⟨cert, sourceReadUnary, graphReadUnary, targetReadUnary, controlReadUnary,
      sealReadUnary⟩

theorem MetricEmbeddingCarrier_graph_distance_control
    {X Y F D R S H C P N sourceGraph targetMetric comparisonSeal graphDistance : BHist} :
    metricEmbeddingFields (MetricEmbeddingUp.mk X Y F D R S H C P N) =
        [X, Y, F, D, R, S, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory F →
          UnaryHistory Y →
            UnaryHistory D →
              UnaryHistory R →
                Cont X F sourceGraph →
                  Cont sourceGraph Y targetMetric →
                    Cont targetMetric D comparisonSeal →
                      Cont comparisonSeal R graphDistance →
                        UnaryHistory sourceGraph ∧ UnaryHistory targetMetric ∧
                          UnaryHistory comparisonSeal ∧ UnaryHistory graphDistance ∧
                            Cont X F sourceGraph ∧ Cont sourceGraph Y targetMetric ∧
                              Cont targetMetric D comparisonSeal ∧
                                Cont comparisonSeal R graphDistance := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fieldRows xUnary fUnary yUnary dUnary rUnary sourceRoute targetRoute comparisonRoute
    graphRoute
  cases fieldRows
  have sourceUnary : UnaryHistory sourceGraph :=
    unary_cont_closed xUnary fUnary sourceRoute
  have targetUnary : UnaryHistory targetMetric :=
    unary_cont_closed sourceUnary yUnary targetRoute
  have comparisonUnary : UnaryHistory comparisonSeal :=
    unary_cont_closed targetUnary dUnary comparisonRoute
  have graphUnary : UnaryHistory graphDistance :=
    unary_cont_closed comparisonUnary rUnary graphRoute
  exact
    ⟨sourceUnary, targetUnary, comparisonUnary, graphUnary, sourceRoute, targetRoute,
      comparisonRoute, graphRoute⟩

end BEDC.Derived.MetricEmbeddingUp
