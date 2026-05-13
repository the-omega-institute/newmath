import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_window_overlap_consumer_amalgamation [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint readA readB overlap
      amalgam : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      Cont endpoint route readA ->
        Cont endpoint containment readB ->
          Cont readA readB overlap ->
            Cont overlap order amalgam ->
              PkgSig bundle amalgam pkg ->
                UnaryHistory readA ∧ UnaryHistory readB ∧ UnaryHistory overlap ∧
                  UnaryHistory amalgam ∧ Cont readA readB overlap ∧
                    Cont overlap order amalgam ∧ PkgSig bundle amalgam pkg := by
  intro packet endpointRouteRead endpointContainmentRead overlapRow amalgamRow amalgamPkg
  obtain ⟨_leftUnary, _rightUnary, orderUnary, containmentUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, endpointUnary, _leftRightOrder, _containmentRow,
    _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  have readAUnary : UnaryHistory readA :=
    unary_cont_closed endpointUnary routeUnary endpointRouteRead
  have readBUnary : UnaryHistory readB :=
    unary_cont_closed endpointUnary containmentUnary endpointContainmentRead
  have overlapUnary : UnaryHistory overlap :=
    unary_cont_closed readAUnary readBUnary overlapRow
  have amalgamUnary : UnaryHistory amalgam :=
    unary_cont_closed overlapUnary orderUnary amalgamRow
  exact
    ⟨readAUnary, readBUnary, overlapUnary, amalgamUnary, overlapRow, amalgamRow, amalgamPkg⟩

end BEDC.Derived.RationalIntervalUp
