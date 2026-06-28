import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateHandoffDecidableNormalFormComparison [AskSetup] [PackageSetup]
    {A K N F C D B T R P L candidateRead frontierRead endpointRead comparisonRead
      blockedRead transportRead replayRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier
        A K N F C D B T R P L bundle pkg ->
      Cont A K candidateRead ->
        Cont candidateRead F frontierRead ->
          Cont frontierRead N endpointRead ->
            Cont endpointRead D comparisonRead ->
              Cont comparisonRead B blockedRead ->
                Cont blockedRead T transportRead ->
                  Cont transportRead R replayRead ->
                    Cont replayRead P publicRead ->
                      PkgSig bundle publicRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row N ∨ hsame row F ∨ hsame row C ∨
                                hsame row D ∨ hsame row B ∨ hsame row T ∨
                                  hsame row R ∨ hsame row P ∨ hsame row L ∨
                                    hsame row comparisonRead ∨ hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont A K candidateRead ∧
                                Cont candidateRead F frontierRead ∧
                                  Cont frontierRead N endpointRead ∧
                                    Cont endpointRead D comparisonRead ∧
                                      Cont comparisonRead B blockedRead ∧
                                        Cont blockedRead T transportRead ∧
                                          Cont transportRead R replayRead ∧
                                            Cont replayRead P publicRead ∧
                                              PkgSig bundle publicRead pkg)
                            hsame ∧
                          UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                            UnaryHistory endpointRead ∧ UnaryHistory comparisonRead ∧
                              UnaryHistory blockedRead ∧ UnaryHistory transportRead ∧
                                UnaryHistory replayRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier candidateRoute frontierRoute endpointRoute comparisonRoute blockedRoute
    transportRoute replayRoute publicRoute publicPkg
  have auditUnary : UnaryHistory A := carrier.left
  have candidateUnary : UnaryHistory K := carrier.right.left
  have endpointUnary : UnaryHistory N := carrier.right.right.left
  have frontierUnary : UnaryHistory F := carrier.right.right.right.left
  have decidableUnary : UnaryHistory D := carrier.right.right.right.right.right.left
  have blockedUnary : UnaryHistory B :=
    carrier.right.right.right.right.right.right.left
  have transportUnary : UnaryHistory T :=
    carrier.right.right.right.right.right.right.right.left
  have replayUnary : UnaryHistory R :=
    carrier.right.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory P :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary candidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary frontierRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed frontierReadUnary endpointUnary endpointRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed endpointReadUnary decidableUnary comparisonRoute
  have blockedReadUnary : UnaryHistory blockedRead :=
    unary_cont_closed comparisonReadUnary blockedUnary blockedRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed blockedReadUnary transportUnary transportRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportReadUnary replayUnary replayRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed replayReadUnary provenanceUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row N ∨ hsame row F ∨ hsame row C ∨
              hsame row D ∨ hsame row B ∨ hsame row T ∨ hsame row R ∨
                hsame row P ∨ hsame row L ∨ hsame row comparisonRead ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A K candidateRead ∧
              Cont candidateRead F frontierRead ∧ Cont frontierRead N endpointRead ∧
                Cont endpointRead D comparisonRead ∧ Cont comparisonRead B blockedRead ∧
                  Cont blockedRead T transportRead ∧ Cont transportRead R replayRead ∧
                    Cont replayRead P publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, candidateRoute, frontierRoute, endpointRoute, comparisonRoute,
          blockedRoute, transportRoute, replayRoute, publicRoute, publicPkg⟩
  }
  exact
    ⟨cert, candidateReadUnary, frontierReadUnary, endpointReadUnary, comparisonReadUnary,
      blockedReadUnary, transportReadUnary, replayReadUnary, publicReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
