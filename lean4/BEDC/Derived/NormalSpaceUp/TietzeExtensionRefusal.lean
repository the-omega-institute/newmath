import BEDC.Derived.NormalSpaceUp.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalSpacePacket_tietze_extension_refusal [AskSetup] [PackageSetup]
    {topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      localName exported separationRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormalSpacePacket topology closedLeft closedRight disjoint openLeft openRight transport
        replay provenance localName exported bundle pkg →
      Cont openLeft openRight separationRead →
        Cont separationRead replay refusalRead →
          PkgSig bundle refusalRead pkg →
            UnaryHistory topology ∧ UnaryHistory closedLeft ∧ UnaryHistory closedRight ∧
              UnaryHistory disjoint ∧ UnaryHistory openLeft ∧ UnaryHistory openRight ∧
                UnaryHistory separationRead ∧ UnaryHistory refusalRead ∧
                  Cont closedLeft closedRight disjoint ∧
                    Cont openLeft openRight separationRead ∧
                      Cont separationRead replay refusalRead ∧
                        PkgSig bundle localName pkg ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet openSeparation separationRefusal refusalPkg
  obtain ⟨topologyUnary, closedLeftUnary, closedRightUnary, disjointUnary, openLeftUnary,
    openRightUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _exportedUnary, closedDisjoint, _openTransport, _transportProvenance,
    _provenanceExported, localNamePkg⟩ := packet
  have separationReadUnary : UnaryHistory separationRead :=
    unary_cont_closed openLeftUnary openRightUnary openSeparation
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed separationReadUnary replayUnary separationRefusal
  exact
    ⟨topologyUnary, closedLeftUnary, closedRightUnary, disjointUnary, openLeftUnary,
      openRightUnary, separationReadUnary, refusalReadUnary, closedDisjoint, openSeparation,
      separationRefusal, localNamePkg, refusalPkg⟩

end BEDC.Derived.NormalSpaceUp
