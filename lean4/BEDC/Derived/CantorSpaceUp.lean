import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CantorSpaceCarrier [AskSetup] [PackageSetup]
    (schedule window boolLedger listSpine endpointExclusion transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory boolLedger ∧
    UnaryHistory listSpine ∧ UnaryHistory endpointExclusion ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont schedule window boolLedger ∧ Cont boolLedger listSpine endpointExclusion ∧
          Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem CantorSpaceCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {schedule window boolLedger listSpine endpointExclusion transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport replay
        provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport
            replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport
            replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport
            replay provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrier, hsame_refl localName⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CantorSpaceCarrier_finite_prefix_cylinder_stability [AskSetup] [PackageSetup]
    {schedule window boolLedger listSpine endpointExclusion transport replay provenance
      localName prefixWindow prefixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport replay
        provenance localName bundle pkg →
      UnaryHistory prefixWindow →
        Cont window prefixWindow prefixRead →
          PkgSig bundle prefixRead pkg →
            UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory boolLedger ∧
              UnaryHistory listSpine ∧ UnaryHistory prefixRead ∧
                Cont window prefixWindow prefixRead ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle prefixRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier prefixWindowUnary prefixCont prefixPkg
  exact ⟨carrier.left,
    carrier.right.left,
    carrier.right.right.left,
    carrier.right.right.right.left,
    unary_cont_closed carrier.right.left prefixWindowUnary prefixCont,
    prefixCont,
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right,
    prefixPkg⟩

theorem CantorSpaceCarrier_prefix_projection_stability [AskSetup] [PackageSetup]
    {schedule window boolLedger listSpine endpointExclusion transport replay provenance
      localName prefixWindow prefixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport replay
        provenance localName bundle pkg →
      UnaryHistory prefixWindow →
        Cont window prefixWindow prefixRead →
          Cont prefixRead replay provenance →
            PkgSig bundle prefixRead pkg →
              UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory boolLedger ∧
                UnaryHistory listSpine ∧ UnaryHistory prefixWindow ∧
                  UnaryHistory prefixRead ∧ UnaryHistory provenance ∧
                    Cont window prefixWindow prefixRead ∧ Cont prefixRead replay provenance ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle prefixRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier prefixWindowUnary prefixCont prefixReplay prefixPkg
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      prefixWindowUnary,
      unary_cont_closed carrier.right.left prefixWindowUnary prefixCont,
      carrier.right.right.right.right.right.right.right.left,
      prefixCont,
      prefixReplay,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right,
      prefixPkg⟩

theorem CantorSpaceCarrier_streamname_prefix_consumer_exhaustion [AskSetup] [PackageSetup]
    {schedule window boolLedger listSpine endpointExclusion transport replay provenance
      localName publicRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CantorSpaceCarrier schedule window boolLedger listSpine endpointExclusion transport replay
        provenance localName bundle pkg →
      Cont schedule window publicRead →
        Cont boolLedger listSpine endpoint →
          PkgSig bundle publicRead pkg →
            PkgSig bundle endpoint pkg →
              UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory boolLedger ∧
                UnaryHistory listSpine ∧ UnaryHistory publicRead ∧ UnaryHistory endpoint ∧
                  Cont schedule window publicRead ∧ Cont boolLedger listSpine endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier publicCont endpointCont publicPkg endpointPkg
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      unary_cont_closed carrier.left carrier.right.left publicCont,
      unary_cont_closed carrier.right.right.left carrier.right.right.right.left endpointCont,
      publicCont,
      endpointCont,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left,
      publicPkg,
      endpointPkg⟩

end BEDC.Derived.CantorSpaceUp
