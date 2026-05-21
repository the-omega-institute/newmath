import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySequenceEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchySequenceEquivalenceCarrier [AskSetup] [PackageSetup]
    (leftSeq rightSeq witness regseq realSeal transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftSeq ∧ UnaryHistory rightSeq ∧ UnaryHistory witness ∧
    UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont leftSeq rightSeq witness ∧ Cont witness regseq realSeal ∧
          Cont realSeal transport route ∧ Cont route nameRow provenance ∧
            PkgSig bundle provenance pkg

theorem CauchySequenceEquivalenceNamecertObligations [AskSetup] [PackageSetup]
    {leftSeq rightSeq witness regseq realSeal transport route provenance nameRow
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceEquivalenceCarrier leftSeq rightSeq witness regseq realSeal transport route
        provenance nameRow bundle pkg ->
      Cont regseq realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row leftSeq ∨ hsame row rightSeq ∨ hsame row endpoint)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                  hsame row endpoint)
              hsame ∧
            UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier regRealEndpoint endpointPkg
  obtain ⟨_leftUnary, _rightUnary, _witnessUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameRowUnary, _leftRightWitness,
    _witnessRegReal, _realTransportRoute, _routeNameProvenance, provenancePkg⟩ :=
    carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed regseqUnary realSealUnary regRealEndpoint
  have sourceEndpoint :
      (fun row : BHist => hsame row endpoint ∧ UnaryHistory row) endpoint := by
    exact ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row leftSeq ∨ hsame row rightSeq ∨ hsame row endpoint)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
              hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, endpointPkg, source.left⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.CauchySequenceEquivalenceUp
