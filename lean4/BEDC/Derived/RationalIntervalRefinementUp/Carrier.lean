import BEDC.Derived.RationalIntervalRefinementUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalIntervalRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalIntervalRefinementCarrier [AskSetup] [PackageSetup]
    (parent child endpointLedger retainedWindow support transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory parent ∧ UnaryHistory child ∧ UnaryHistory endpointLedger ∧
    UnaryHistory retainedWindow ∧ UnaryHistory support ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont parent child endpointLedger ∧ Cont endpointLedger retainedWindow support ∧
          Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem RationalIntervalRefinementNestedWindow [AskSetup] [PackageSetup]
    {parent child endpointLedger retainedWindow support transport replay provenance localName
      retainedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalRefinementCarrier parent child endpointLedger retainedWindow support
        transport replay provenance localName bundle pkg ->
      Cont child endpointLedger retainedRead ->
        PkgSig bundle retainedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row parent ∨ hsame row child ∨ hsame row endpointLedger ∨
                  hsame row retainedWindow ∨ hsame row support ∨ hsame row retainedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont parent child endpointLedger ∧
                  Cont endpointLedger retainedWindow support ∧
                    Cont child endpointLedger retainedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle retainedRead pkg)
              hsame ∧
            UnaryHistory retainedRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier childEndpointRetained retainedPkg
  obtain ⟨parentUnary, childUnary, endpointUnary, _retainedWindowUnary, _supportUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, parentChildEndpoint,
    endpointRetainedSupport, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
    carrier
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed childUnary endpointUnary childEndpointRetained
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row parent ∨ hsame row child ∨ hsame row endpointLedger ∨
            hsame row retainedWindow ∨ hsame row support ∨ hsame row retainedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont parent child endpointLedger ∧
            Cont endpointLedger retainedWindow support ∧
              Cont child endpointLedger retainedRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle retainedRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro retainedRead ⟨hsame_refl retainedRead, retainedUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, parentChildEndpoint, endpointRetainedSupport,
            childEndpointRetained, provenancePkg, retainedPkg⟩
    }
  exact ⟨cert, retainedUnary⟩

end BEDC.Derived.RationalIntervalRefinementUp
