import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NiemytzkiPlaneUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NiemytzkiPlaneNameCertObligations [AskSetup] [PackageSetup]
    {upper boundary tangent coordinate classifier transport replay provenance localName
      namedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory upper ->
      UnaryHistory boundary ->
        UnaryHistory tangent ->
          UnaryHistory coordinate ->
            UnaryHistory classifier ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  UnaryHistory provenance ->
                    UnaryHistory localName ->
                      Cont boundary tangent coordinate ->
                        Cont classifier replay namedRoute ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row upper ∨ hsame row boundary ∨
                                      hsame row tangent ∨ hsame row coordinate ∨
                                        hsame row classifier ∨ hsame row transport ∨
                                          hsame row replay ∨ hsame row provenance ∨
                                            hsame row localName ∨ hsame row namedRoute)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont boundary tangent coordinate ∧
                                      Cont classifier replay namedRoute ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory namedRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _upperUnary boundaryUnary tangentUnary _coordinateUnary classifierUnary
    _transportUnary replayUnary provenanceUnary _localNameUnary boundaryTangentCoordinate
    classifierReplayNamed provenancePkg localNamePkg
  have coordinateUnary : UnaryHistory coordinate :=
    unary_cont_closed boundaryUnary tangentUnary boundaryTangentCoordinate
  have namedRouteUnary : UnaryHistory namedRoute :=
    unary_cont_closed classifierUnary replayUnary classifierReplayNamed
  have sourceNamed : hsame namedRoute namedRoute ∧ UnaryHistory namedRoute :=
    ⟨hsame_refl namedRoute, namedRouteUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row upper ∨ hsame row boundary ∨ hsame row tangent ∨
              hsame row coordinate ∨ hsame row classifier ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row namedRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundary tangent coordinate ∧
              Cont classifier replay namedRoute ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRoute sourceNamed
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryTangentCoordinate, classifierReplayNamed, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, namedRouteUnary⟩

end BEDC.Derived.NiemytzkiPlaneUp
