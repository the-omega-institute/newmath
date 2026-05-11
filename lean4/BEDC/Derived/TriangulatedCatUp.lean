import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TriangulatedCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TriangulatedCatFiniteCarrier [AskSetup] [PackageSetup]
    (category derived shift triangle morphism classifier contRows provenance endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory derived ∧ UnaryHistory shift ∧
    UnaryHistory triangle ∧ UnaryHistory morphism ∧ UnaryHistory classifier ∧
      UnaryHistory contRows ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        Cont category derived shift ∧ Cont shift triangle morphism ∧
          Cont morphism classifier contRows ∧ Cont contRows provenance endpoint ∧
            PkgSig probe endpoint pkg

theorem TriangulatedCatFiniteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {category derived shift triangle morphism classifier contRows provenance endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
        contRows provenance endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
              contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
              contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            TriangulatedCatFiniteCarrier category derived shift triangle morphism classifier
              contRows provenance endpoint probe pkg ∧ hsame row endpoint)
          hsame ∧
        Cont category derived shift ∧ Cont shift triangle morphism ∧
          Cont morphism classifier contRows ∧ Cont contRows provenance endpoint ∧
            PkgSig probe endpoint pkg := by
  intro carrier
  cases carrier with
  | intro categoryUnary rest =>
      cases rest with
      | intro derivedUnary rest =>
          cases rest with
          | intro shiftUnary rest =>
              cases rest with
              | intro triangleUnary rest =>
                  cases rest with
                  | intro morphismUnary rest =>
                      cases rest with
                      | intro classifierUnary rest =>
                          cases rest with
                          | intro contRowsUnary rest =>
                              cases rest with
                              | intro provenanceUnary rest =>
                                  cases rest with
                                  | intro endpointUnary rest =>
                                      cases rest with
                                      | intro categoryDerivedShift rest =>
                                          cases rest with
                                          | intro shiftTriangleMorphism rest =>
                                              cases rest with
                                              | intro morphismClassifierRows rest =>
                                                  cases rest with
                                                  | intro rowsProvenanceEndpoint pkgSig =>
                                                      have carrierAgain :
                                                          TriangulatedCatFiniteCarrier category
                                                            derived shift triangle morphism
                                                            classifier contRows provenance
                                                            endpoint probe pkg :=
                                                        ⟨categoryUnary, derivedUnary, shiftUnary,
                                                          triangleUnary, morphismUnary,
                                                          classifierUnary, contRowsUnary,
                                                          provenanceUnary, endpointUnary,
                                                          categoryDerivedShift,
                                                          shiftTriangleMorphism,
                                                          morphismClassifierRows,
                                                          rowsProvenanceEndpoint, pkgSig⟩
                                                      have cert :
                                                          SemanticNameCert
                                                            (fun row : BHist =>
                                                              TriangulatedCatFiniteCarrier
                                                                category derived shift triangle
                                                                morphism classifier contRows
                                                                provenance endpoint probe pkg ∧
                                                                hsame row endpoint)
                                                            (fun row : BHist =>
                                                              TriangulatedCatFiniteCarrier
                                                                category derived shift triangle
                                                                morphism classifier contRows
                                                                provenance endpoint probe pkg ∧
                                                                hsame row endpoint)
                                                            (fun row : BHist =>
                                                              TriangulatedCatFiniteCarrier
                                                                category derived shift triangle
                                                                morphism classifier contRows
                                                                provenance endpoint probe pkg ∧
                                                                hsame row endpoint)
                                                            hsame := {
                                                        core := {
                                                          carrier_inhabited :=
                                                            Exists.intro endpoint
                                                              (And.intro carrierAgain
                                                                (hsame_refl endpoint))
                                                          equiv_refl := by
                                                            intro row _source
                                                            exact hsame_refl row
                                                          equiv_symm := by
                                                            intro _row _row' same
                                                            exact hsame_symm same
                                                          equiv_trans := by
                                                            intro _row _row' _row'' sameLeft
                                                              sameRight
                                                            exact hsame_trans sameLeft sameRight
                                                          carrier_respects_equiv := by
                                                            intro _row _row' same source
                                                            exact And.intro source.left
                                                              (hsame_trans (hsame_symm same)
                                                                source.right)
                                                        }
                                                        pattern_sound := by
                                                          intro _row source
                                                          exact source
                                                        ledger_sound := by
                                                          intro _row source
                                                          exact source
                                                      }
                                                      exact
                                                        And.intro cert
                                                          (And.intro categoryDerivedShift
                                                            (And.intro shiftTriangleMorphism
                                                              (And.intro morphismClassifierRows
                                                                (And.intro rowsProvenanceEndpoint
                                                                  pkgSig))))

end BEDC.Derived.TriangulatedCatUp
