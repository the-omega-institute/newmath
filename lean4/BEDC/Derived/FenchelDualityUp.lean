import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FenchelDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FenchelDualityCarrier [AskSetup] [PackageSetup]
    (primal dual pairing comparison epigraph cone provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory pairing ∧
    UnaryHistory comparison ∧ UnaryHistory epigraph ∧ UnaryHistory cone ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont primal dual pairing ∧
        Cont pairing comparison epigraph ∧ Cont epigraph cone provenance ∧
          Cont provenance comparison endpoint ∧ PkgSig bundle endpoint pkg

theorem FenchelDualityCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {primal dual pairing comparison epigraph cone provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance endpoint
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance e
                bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance e
                bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance e
                bundle pkg ∧ hsame row e)
          hsame ∧
        Cont primal dual pairing ∧ Cont pairing comparison epigraph ∧
          Cont epigraph cone provenance ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance e
            bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          exists e : BHist,
            FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance e
              bundle pkg ∧ hsame row e)
        (fun row : BHist =>
          exists e : BHist,
            FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance e
              bundle pkg ∧ hsame row e)
        (fun row : BHist =>
          exists e : BHist,
            FenchelDualityCarrier primal dual pairing comparison epigraph cone provenance e
              bundle pkg ∧ hsame row e)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases source with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left (hsame_trans (hsame_symm sameRows) endpointData.right))
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
      (And.intro carrier.right.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right.right.right.right.right.left
            carrier.right.right.right.right.right.right.right.right.right.right.right.right)))

def FenchelDualityPrimalDualPacket [AskSetup] [PackageSetup]
    (primal dual pairing comparison epigraph cone ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory comparison ∧
    UnaryHistory epigraph ∧ UnaryHistory cone ∧ Cont primal dual pairing ∧
      Cont pairing comparison epigraph ∧ Cont epigraph cone ledger ∧
        PkgSig bundle ledger pkg

theorem FenchelDualityPrimalDualPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {primal dual pairing comparison epigraph cone ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FenchelDualityPrimalDualPacket primal dual pairing comparison epigraph cone ledger
        bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row ledger)
          (fun row : BHist => hsame row ledger) (fun row : BHist => hsame row ledger)
          hsame ∧
        UnaryHistory primal ∧ UnaryHistory dual ∧ Cont primal dual pairing ∧
          Cont epigraph cone ledger ∧ PkgSig bundle ledger pkg := by
  intro packet
  have primalUnary : UnaryHistory primal :=
    packet.left
  have dualUnary : UnaryHistory dual :=
    packet.right.left
  have primalDualRow : Cont primal dual pairing :=
    packet.right.right.right.right.right.left
  have epigraphConeRow : Cont epigraph cone ledger :=
    packet.right.right.right.right.right.right.right.left
  have packageRow : PkgSig bundle ledger pkg :=
    packet.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert (fun row : BHist => hsame row ledger)
          (fun row : BHist => hsame row ledger) (fun row : BHist => hsame row ledger)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger (hsame_refl ledger)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro primalUnary
      (And.intro dualUnary
        (And.intro primalDualRow (And.intro epigraphConeRow packageRow))))

end BEDC.Derived.FenchelDualityUp
