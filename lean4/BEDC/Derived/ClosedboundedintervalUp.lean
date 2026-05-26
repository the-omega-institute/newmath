import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalPacket [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory rational ∧
    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ UnaryHistory exported ∧ Cont lower upper order ∧
          Cont order rational dyadic ∧ Cont stream readback sealRow ∧
            Cont transport replay provenance ∧ Cont provenance localName exported ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem ClosedBoundedIntervalPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
              transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
              transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
              transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName (And.intro packet (hsame_refl localName))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem ClosedBoundedIntervalPacket_endpoint_transport [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg)
    {lower' upper' order' : BHist}
    (hl : hsame lower lower') (hu : hsame upper upper')
    (horder' : Cont lower' upper' order') : hsame order order' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  cases hl
  cases hu
  exact
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left.trans
      horder'.symm

theorem ClosedBoundedIntervalPacket_root_source_split [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg) :
    hsame dyadic (append (append lower upper) rational) ∧
      hsame sealRow (append stream readback) ∧
        hsame exported (append (append transport replay) localName) := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  constructor
  · exact
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left.trans
        (congrArg (fun row : BHist => append row rational)
          packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left)
  · constructor
    · exact
        packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
    · exact
        packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left.trans
          (congrArg (fun row : BHist => append row localName)
            packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left)

theorem ClosedBoundedIntervalPacket_root_obligation_spine [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported endpointSource containmentSource sealSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont lower upper endpointSource ->
        Cont rational dyadic containmentSource ->
          Cont stream readback sealSource ->
            PkgSig bundle endpointSource pkg ->
              PkgSig bundle containmentSource pkg ->
                PkgSig bundle sealSource pkg ->
                  UnaryHistory endpointSource ∧ UnaryHistory containmentSource ∧
                    UnaryHistory sealSource ∧ Cont lower upper endpointSource ∧
                      Cont rational dyadic containmentSource ∧ Cont stream readback sealSource ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle endpointSource pkg ∧
                          PkgSig bundle containmentSource pkg ∧ PkgSig bundle sealSource pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet endpointRoute containmentRoute sealRoute endpointPkg containmentPkg sealPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _carrierEndpointRoute, _carrierContainmentRoute,
    _carrierSealRoute, _carrierReplayRoute, _carrierNameRoute, provenancePkg, _localNamePkg⟩ :=
      packet
  have endpointUnary : UnaryHistory endpointSource :=
    unary_cont_closed lowerUnary upperUnary endpointRoute
  have containmentUnary : UnaryHistory containmentSource :=
    unary_cont_closed rationalUnary dyadicUnary containmentRoute
  have sealUnary : UnaryHistory sealSource :=
    unary_cont_closed streamUnary readbackUnary sealRoute
  exact
    ⟨endpointUnary, containmentUnary, sealUnary, endpointRoute, containmentRoute, sealRoute,
      provenancePkg, endpointPkg, containmentPkg, sealPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
