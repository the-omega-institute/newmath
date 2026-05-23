import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCompletionEndpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyCompletionEndpointCarrier [AskSetup] [PackageSetup]
    (regular limitSeal exactBoundary unit terminalSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  UnaryHistory regular ∧ UnaryHistory limitSeal ∧ UnaryHistory exactBoundary ∧
    UnaryHistory unit ∧ UnaryHistory terminalSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont regular limitSeal exactBoundary ∧ Cont exactBoundary unit terminalSeal ∧
          Cont unit terminalSeal replay ∧ hsame transport transport ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem RegularCauchyCompletionEndpointCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {regular limitSeal exactBoundary unit terminalSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionEndpointCarrier regular limitSeal exactBoundary unit
        terminalSeal transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row terminalSeal ∧
              RegularCauchyCompletionEndpointCarrier regular limitSeal exactBoundary unit
                terminalSeal transport replay provenance localName bundle pkg)
          (fun row : BHist => hsame row terminalSeal ∧ Cont unit terminalSeal replay)
          (fun row : BHist => hsame row terminalSeal ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory regular ∧ UnaryHistory limitSeal ∧ UnaryHistory exactBoundary ∧
          UnaryHistory unit ∧ UnaryHistory terminalSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨regularUnary, limitSealUnary, exactBoundaryUnary, unitUnary, terminalSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _exactBoundaryRoute,
    _terminalSealRoute, unitTerminalReplay, _transportSame, provenancePkg,
    _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row terminalSeal ∧
            RegularCauchyCompletionEndpointCarrier regular limitSeal exactBoundary unit
              terminalSeal transport replay provenance localName bundle pkg)
        (fun row : BHist => hsame row terminalSeal ∧ Cont unit terminalSeal replay)
        (fun row : BHist => hsame row terminalSeal ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalSeal ⟨hsame_refl terminalSeal, carrierWitness⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, unitTerminalReplay⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, regularUnary, limitSealUnary, exactBoundaryUnary, unitUnary, terminalSealUnary,
      provenancePkg⟩

end BEDC.Derived.RegularCauchyCompletionEndpointUp
