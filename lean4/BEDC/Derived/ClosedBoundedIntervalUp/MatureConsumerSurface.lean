import BEDC.Derived.ClosedboundedintervalUp
import BEDC.Derived.ClosedBoundedIntervalUp.PublicBridgeBoundary
import BEDC.Derived.ClosedBoundedIntervalUp.PublicConsumerSurface

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_mature_consumer_surface [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported publicRead finiteCoverRead locatedCoverRead modulusRead compactRead
      netRead coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont exported localName publicRead ->
        Cont publicRead dyadic finiteCoverRead ->
          Cont finiteCoverRead stream locatedCoverRead ->
            Cont locatedCoverRead sealRow modulusRead ->
              Cont modulusRead readback compactRead ->
                Cont exported dyadic netRead ->
                  Cont exported stream coverRead ->
                    Cont netRead coverRead compactRead ->
                      PkgSig bundle compactRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row publicRead ∨ hsame row finiteCoverRead ∨
                                hsame row locatedCoverRead ∨ hsame row modulusRead ∨
                                  hsame row compactRead ∨
                                    Cont modulusRead readback compactRead ∨
                                      Cont netRead coverRead compactRead)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle compactRead pkg ∧ hsame row compactRead)
                            hsame ∧
                          UnaryHistory publicRead ∧ UnaryHistory finiteCoverRead ∧
                            UnaryHistory locatedCoverRead ∧ UnaryHistory modulusRead ∧
                              UnaryHistory compactRead ∧ UnaryHistory netRead ∧
                                UnaryHistory coverRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet publicRoute finiteRoute locatedRoute modulusRoute compactRoute
    exportedDyadicNet exportedStreamCover netCoverCompact compactPkg
  obtain ⟨_publicCert, publicUnary, finiteUnary, locatedUnary, modulusUnary, compactUnary⟩ :=
    ClosedBoundedIntervalPublicBridgeBoundary (lower := lower) (upper := upper)
      (order := order) (rational := rational) (dyadic := dyadic) (stream := stream)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (replay := replay) (provenance := provenance) (localName := localName)
      (exported := exported) (publicRead := publicRead) (finiteCoverRead := finiteCoverRead)
      (locatedCoverRead := locatedCoverRead) (modulusRead := modulusRead)
      (compactRead := compactRead) (bundle := bundle) (pkg := pkg)
      packet publicRoute finiteRoute locatedRoute modulusRoute compactRoute compactPkg
  obtain ⟨publicSurfaceCert, netUnary, coverUnary, _surfaceCompactUnary⟩ :=
    ClosedBoundedIntervalPublicConsumerSurface (lower := lower) (upper := upper)
      (order := order) (rational := rational) (dyadic := dyadic) (stream := stream)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (replay := replay) (provenance := provenance) (localName := localName)
      (exported := exported) (netRead := netRead) (coverRead := coverRead)
      (compactRead := compactRead) (bundle := bundle) (pkg := pkg)
      packet exportedDyadicNet exportedStreamCover netCoverCompact compactPkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row publicRead ∨ hsame row finiteCoverRead ∨
              hsame row locatedCoverRead ∨ hsame row modulusRead ∨
                hsame row compactRead ∨ Cont modulusRead readback compactRead ∨
                  Cont netRead coverRead compactRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
              hsame row compactRead)
          hsame := {
    core := publicSurfaceCert.core
    pattern_sound := by
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr netCoverCompact)))))
    ledger_sound := publicSurfaceCert.ledger_sound
  }
  exact
    ⟨cert, publicUnary, finiteUnary, locatedUnary, modulusUnary, compactUnary, netUnary,
      coverUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
