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

end BEDC.Derived.ClosedboundedintervalUp
