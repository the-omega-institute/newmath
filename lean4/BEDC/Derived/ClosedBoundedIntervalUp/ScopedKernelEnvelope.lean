import BEDC.Derived.ClosedboundedintervalUp
import BEDC.Derived.ClosedBoundedIntervalUp.ObligationClosure

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_scoped_kernel_envelope [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported grid cell sourceWindow sourceOut netRead coverRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont order dyadic grid →
        Cont grid stream cell →
          Cont dyadic stream sourceWindow →
            Cont sourceWindow sealRow sourceOut →
              Cont exported dyadic netRead →
                Cont exported stream coverRead →
                  Cont netRead coverRead compactRead →
                    PkgSig bundle cell pkg →
                      PkgSig bundle sourceOut pkg →
                        PkgSig bundle compactRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row lower ∨ hsame row upper ∨ hsame row dyadic ∨
                                  Cont exported dyadic netRead ∨
                                    Cont exported stream coverRead ∨
                                      Cont netRead coverRead compactRead)
                              (fun row : BHist =>
                                PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                                  hsame row compactRead)
                              hsame ∧
                            UnaryHistory grid ∧ UnaryHistory cell ∧
                              UnaryHistory sourceWindow ∧ UnaryHistory sourceOut ∧
                                UnaryHistory netRead ∧ UnaryHistory coverRead ∧
                                  UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet orderDyadicGrid gridStreamCell dyadicStreamSource sourceSealOut
    exportedDyadicNet exportedStreamCover netCoverCompact cellPkg sourceOutPkg compactPkg
  have closure :=
    ClosedBoundedIntervalPacket_obligation_closure
      (lower := lower) (upper := upper) (order := order) (rational := rational)
      (dyadic := dyadic) (stream := stream) (readback := readback) (sealRow := sealRow)
      (transport := transport) (replay := replay) (provenance := provenance)
      (localName := localName) (exported := exported) (netRead := netRead)
      (coverRead := coverRead) (compactRead := compactRead) (bundle := bundle) (pkg := pkg)
      packet exportedDyadicNet exportedStreamCover netCoverCompact compactPkg
  obtain ⟨_lowerUnary, _upperUnary, orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, _readbackUnary, sealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute,
    _containmentRoute, _sealRoute, _replayRoute, _nameRoute, _provenancePkg,
    _localNamePkg⟩ := packet
  have gridUnary : UnaryHistory grid :=
    unary_cont_closed orderUnary dyadicUnary orderDyadicGrid
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed gridUnary streamUnary gridStreamCell
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have sourceOutUnary : UnaryHistory sourceOut :=
    unary_cont_closed sourceWindowUnary sealUnary sourceSealOut
  obtain ⟨cert, netUnary, coverUnary, compactUnary⟩ := closure
  exact
    ⟨cert, gridUnary, cellUnary, sourceWindowUnary, sourceOutUnary, netUnary, coverUnary,
      compactUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
