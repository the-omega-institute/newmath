import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_scoped_source_package [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported grid cell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont order dyadic grid ->
        Cont grid stream cell ->
          PkgSig bundle cell pkg ->
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
                  UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
                    UnaryHistory grid ∧ UnaryHistory cell ∧ Cont lower upper order ∧
                      Cont order rational dyadic ∧ Cont stream readback sealRow ∧
                        Cont transport replay provenance ∧ Cont provenance localName exported ∧
                          Cont order dyadic grid ∧ Cont grid stream cell ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                              PkgSig bundle cell pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet orderDyadicGrid gridStreamCell cellPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, transportUnary, replayUnary, provenanceUnary,
    localNameUnary, _exportedUnary, endpointRoute, containmentRoute, sealRowRoute,
    replayRoute, nameRoute, provenancePkg, localNamePkg⟩ := packet
  have gridUnary : UnaryHistory grid :=
    unary_cont_closed orderUnary dyadicUnary orderDyadicGrid
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed gridUnary streamUnary gridStreamCell
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, transportUnary, replayUnary, provenanceUnary,
      localNameUnary, gridUnary, cellUnary, endpointRoute, containmentRoute,
      sealRowRoute, replayRoute, nameRoute, orderDyadicGrid, gridStreamCell,
      provenancePkg, localNamePkg, cellPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
