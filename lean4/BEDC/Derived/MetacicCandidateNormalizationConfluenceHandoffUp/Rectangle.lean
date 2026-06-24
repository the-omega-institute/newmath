import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceRectangle [AskSetup] [PackageSetup]
    {A K N F C D B T R P L candidateRead frontierRead confluenceRead decidableRead
      blockerRead rectangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R
        P L bundle pkg ->
      Cont A K candidateRead ->
        Cont candidateRead F frontierRead ->
          Cont frontierRead C confluenceRead ->
            Cont confluenceRead D decidableRead ->
              Cont confluenceRead B blockerRead ->
                Cont decidableRead blockerRead rectangleRead ->
                  PkgSig bundle rectangleRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row rectangleRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨
                            hsame row B ∨ hsame row rectangleRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont frontierRead C confluenceRead ∧
                            Cont confluenceRead D decidableRead ∧
                              Cont confluenceRead B blockerRead ∧
                                Cont decidableRead blockerRead rectangleRead ∧
                                  PkgSig bundle rectangleRead pkg)
                        hsame ∧
                      UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                        UnaryHistory confluenceRead ∧ UnaryHistory decidableRead ∧
                          UnaryHistory blockerRead ∧ UnaryHistory rectangleRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier candidateRoute frontierRoute confluenceRoute decidableRoute blockerRoute
    rectangleRoute rectanglePkg
  obtain ⟨auditUnary, candidateUnary, _normalUnary, frontierUnary, confluenceUnary,
    decidableUnary, blockerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary candidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary frontierRoute
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed frontierReadUnary confluenceUnary confluenceRoute
  have decidableReadUnary : UnaryHistory decidableRead :=
    unary_cont_closed confluenceReadUnary decidableUnary decidableRoute
  have blockerReadUnary : UnaryHistory blockerRead :=
    unary_cont_closed confluenceReadUnary blockerUnary blockerRoute
  have rectangleReadUnary : UnaryHistory rectangleRead :=
    unary_cont_closed decidableReadUnary blockerReadUnary rectangleRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rectangleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨ hsame row B ∨
              hsame row rectangleRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontierRead C confluenceRead ∧
              Cont confluenceRead D decidableRead ∧ Cont confluenceRead B blockerRead ∧
                Cont decidableRead blockerRead rectangleRead ∧
                  PkgSig bundle rectangleRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rectangleRead ⟨hsame_refl rectangleRead, rectangleReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, confluenceRoute, decidableRoute, blockerRoute, rectangleRoute,
          rectanglePkg⟩
  }
  exact
    ⟨cert, candidateReadUnary, frontierReadUnary, confluenceReadUnary, decidableReadUnary,
      blockerReadUnary, rectangleReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
