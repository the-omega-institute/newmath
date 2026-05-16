import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionObstructionSiblingRoute [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert obstructionRead endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont cert provenance obstructionRead →
        Cont obstructionRead route endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row cert ∧
                    HaltingDistinctionCarrier question trace diagonal halt classifier route
                      provenance cert bundle pkg)
                (fun row : BHist =>
                  hsame row cert ∧ UnaryHistory row ∧
                    Cont cert provenance obstructionRead)
                (fun _row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                    Cont obstructionRead route endpoint)
                hsame ∧
              UnaryHistory obstructionRead ∧ UnaryHistory endpoint ∧
              Cont cert provenance obstructionRead ∧ Cont obstructionRead route endpoint ∧
              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier certProvenanceObstruction obstructionRouteEndpoint endpointPkg
  have carrierPacket :
      HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg :=
    carrier
  obtain ⟨_questionUnary, _traceUnary, _diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, provenanceUnary, certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed certUnary provenanceUnary certProvenanceObstruction
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed obstructionUnary routeUnary obstructionRouteEndpoint
  have certSource :
      hsame cert cert ∧
        HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
          bundle pkg :=
    ⟨hsame_refl cert, carrierPacket⟩
  have semanticCert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cert ∧
              HaltingDistinctionCarrier question trace diagonal halt classifier route provenance
                cert bundle pkg)
          (fun row : BHist =>
            hsame row cert ∧ UnaryHistory row ∧ Cont cert provenance obstructionRead)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
              Cont obstructionRead route endpoint)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro cert certSource
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro row source
      have rowSameCert : hsame row cert := source.left
      exact
        ⟨rowSameCert, unary_transport certUnary (hsame_symm rowSameCert),
          certProvenanceObstruction⟩
    · intro _row _source
      exact ⟨provenancePkg, endpointPkg, obstructionRouteEndpoint⟩
  exact
    ⟨semanticCert, obstructionUnary, endpointUnary, certProvenanceObstruction,
      obstructionRouteEndpoint, endpointPkg⟩

end BEDC.Derived.HaltingDistinctionUp
