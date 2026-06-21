import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ForwardBindingGapLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ForwardBindingGapLedgerCarrier [AskSetup] [PackageSetup]
    (commit record gap refusal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory commit ∧ UnaryHistory record ∧ UnaryHistory gap ∧
    UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont commit record gap ∧
        Cont gap refusal replay ∧ PkgSig bundle provenance pkg

theorem ForwardBindingGapLedgerNameCertObligations [AskSetup] [PackageSetup]
    {commit record gap refusal transport replay provenance localName citation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ForwardBindingGapLedgerCarrier commit record gap refusal transport replay provenance
        localName bundle pkg →
      Cont refusal transport citation →
      PkgSig bundle citation pkg →
      SemanticNameCert
          (fun row : BHist => hsame row citation ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row commit ∨ hsame row record ∨ hsame row gap ∨
              hsame row refusal ∨ hsame row citation)
          (fun row : BHist => PkgSig bundle citation pkg ∧ hsame row citation)
          hsame ∧
        UnaryHistory commit ∧ UnaryHistory record ∧ UnaryHistory gap ∧
          UnaryHistory refusal ∧ UnaryHistory citation ∧ Cont commit record gap ∧
            Cont gap refusal replay ∧ Cont refusal transport citation ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle citation pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier refusalTransport citationPkg
  have commitUnary : UnaryHistory commit := carrier.left
  have recordUnary : UnaryHistory record := carrier.right.left
  have gapUnary : UnaryHistory gap := carrier.right.right.left
  have refusalUnary : UnaryHistory refusal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have citationUnary : UnaryHistory citation :=
    unary_cont_closed refusalUnary transportUnary refusalTransport
  have commitRoute : Cont commit record gap :=
    carrier.right.right.right.right.right.right.right.right.left
  have refusalRoute : Cont gap refusal replay :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row citation ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row commit ∨ hsame row record ∨ hsame row gap ∨
              hsame row refusal ∨ hsame row citation)
          (fun row : BHist => PkgSig bundle citation pkg ∧ hsame row citation)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro citation ⟨hsame_refl citation, citationUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row other same
          exact hsame_symm same
        equiv_trans := by
          intro row other third sameRO sameOT
          exact hsame_trans sameRO sameOT
        carrier_respects_equiv := by
          intro row other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro row source
        exact ⟨citationPkg, source.left⟩
    }
  exact
    ⟨cert, commitUnary, recordUnary, gapUnary, refusalUnary, citationUnary, commitRoute,
      refusalRoute, refusalTransport, provenancePkg, citationPkg⟩

end BEDC.Derived.ForwardBindingGapLedgerUp
