import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive FSigmaSetUp : Type where
  | carrier

namespace FSigmaSetUp

def FSigmaSetCarrier [AskSetup] [PackageSetup]
    (topology borel zeroSet gdelta schedule windows transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory topology ∧ UnaryHistory borel ∧ UnaryHistory zeroSet ∧
    UnaryHistory gdelta ∧ UnaryHistory schedule ∧ UnaryHistory windows ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem FSigmaSetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {topology borel zeroSet gdelta schedule windows transport replay provenance localName
      closedPrefix borelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FSigmaSetCarrier topology borel zeroSet gdelta schedule windows transport replay
      provenance localName bundle pkg ->
      Cont topology schedule windows ->
        Cont windows zeroSet closedPrefix ->
          Cont closedPrefix borel borelRead ->
            PkgSig bundle borelRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row borelRead ∧ UnaryHistory row)
                    (fun row : BHist => hsame row borelRead ∧ Cont topology schedule windows)
                    (fun row : BHist => hsame row borelRead ∧ PkgSig bundle borelRead pkg)
                    hsame ∧
                UnaryHistory closedPrefix ∧ UnaryHistory borelRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier topologyScheduleRoute closedPrefixRoute borelReadRoute borelReadPkg
  obtain ⟨topologyUnary, borelUnary, zeroSetUnary, _gdeltaUnary, scheduleUnary,
    windowsUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg, _localNamePkg⟩ := carrier
  have _windowsUnaryFromRoute : UnaryHistory windows :=
    unary_cont_closed topologyUnary scheduleUnary topologyScheduleRoute
  have closedPrefixUnary : UnaryHistory closedPrefix :=
    unary_cont_closed windowsUnary zeroSetUnary closedPrefixRoute
  have borelReadUnary : UnaryHistory borelRead :=
    unary_cont_closed closedPrefixUnary borelUnary borelReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row borelRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row borelRead ∧ Cont topology schedule windows)
          (fun row : BHist => hsame row borelRead ∧ PkgSig bundle borelRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro borelRead ⟨hsame_refl borelRead, borelReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, topologyScheduleRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, borelReadPkg⟩
  }
  exact ⟨cert, closedPrefixUnary, borelReadUnary⟩

end FSigmaSetUp

end BEDC.Derived
