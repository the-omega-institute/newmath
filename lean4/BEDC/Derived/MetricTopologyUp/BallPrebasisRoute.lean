import BEDC.FKernel.Package
import BEDC.Derived.MetricTopologyUp.BallBasisScope

namespace BEDC.Derived.MetricTopologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricTopologyCarrier [AskSetup] [PackageSetup]
    (metric ball topology realRadius ratRadius transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory metric ∧ UnaryHistory ball ∧ UnaryHistory topology ∧
    UnaryHistory realRadius ∧ UnaryHistory ratRadius ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont metric ball topology ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem MetricTopologyBallPrebasisRoute [AskSetup] [PackageSetup]
    {metric ball topology realRadius ratRadius transport replay provenance localName ballRead
      openRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricTopologyCarrier metric ball topology realRadius ratRadius transport replay provenance
        localName bundle pkg →
      Cont metric ball ballRead →
        Cont ballRead topology openRead →
          PkgSig bundle openRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row openRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row ball ∨ hsame row topology ∨
                    hsame row realRadius ∨ hsame row ratRadius ∨ hsame row ballRead ∨
                      hsame row openRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont metric ball ballRead ∧
                    Cont ballRead topology openRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle openRead pkg)
                hsame ∧
              UnaryHistory ballRead ∧ UnaryHistory openRead := by
  -- BEDC touchpoint anchor: MetricTopologyCarrier BHist ProbeBundle Pkg Cont PkgSig hsame
  intro carrier metricBallRead ballTopologyOpen openPkg
  obtain ⟨metricUnary, ballUnary, topologyUnary, _realUnary, _ratUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _metricBallTopology,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed metricUnary ballUnary metricBallRead
  have openReadUnary : UnaryHistory openRead :=
    unary_cont_closed ballReadUnary topologyUnary ballTopologyOpen
  have openSource : hsame openRead openRead ∧ UnaryHistory openRead :=
    ⟨hsame_refl openRead, openReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row openRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row metric ∨ hsame row ball ∨ hsame row topology ∨
            hsame row realRadius ∨ hsame row ratRadius ∨ hsame row ballRead ∨
              hsame row openRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont metric ball ballRead ∧ Cont ballRead topology openRead ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle openRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro openRead openSource
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, metricBallRead, ballTopologyOpen, provenancePkg, openPkg⟩
  }
  exact ⟨cert, ballReadUnary, openReadUnary⟩

end BEDC.Derived.MetricTopologyUp
