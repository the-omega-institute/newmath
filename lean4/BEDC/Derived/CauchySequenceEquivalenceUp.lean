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
    (x y streamX streamY tolerance classifier sealRow transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory streamX ∧ UnaryHistory streamY ∧
    UnaryHistory tolerance ∧ UnaryHistory classifier ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameRow ∧ Cont x streamX tolerance ∧ Cont y streamY classifier ∧
          Cont classifier sealRow route ∧ Cont route nameRow provenance ∧
            PkgSig bundle provenance pkg

theorem CauchySequenceEquivalenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {x y streamX streamY tolerance classifier sealRow transport route provenance nameRow handoff :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceEquivalenceCarrier x y streamX streamY tolerance classifier sealRow transport
        route provenance nameRow bundle pkg ->
      Cont classifier sealRow handoff ->
        PkgSig bundle handoff pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row x ∨ hsame row y ∨ hsame row tolerance ∨
                  hsame row classifier ∨ hsame row handoff)
              (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
              hsame ∧
            UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory streamX ∧
              UnaryHistory streamY ∧ UnaryHistory tolerance ∧ UnaryHistory classifier ∧
                UnaryHistory sealRow ∧ UnaryHistory handoff ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier classifierSealHandoff handoffPkg
  obtain ⟨xUnary, yUnary, streamXUnary, streamYUnary, toleranceUnary, classifierUnary,
    sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    _xStreamTolerance, _yStreamClassifier, _classifierSealRoute, _routeNameProvenance,
    provenancePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed classifierUnary sealUnary classifierSealHandoff
  have sourceHandoff :
      (fun row : BHist => hsame row handoff ∧ UnaryHistory row) handoff := by
    exact ⟨hsame_refl handoff, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row x ∨ hsame row y ∨ hsame row tolerance ∨ hsame row classifier ∨
              hsame row handoff)
          (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff sourceHandoff
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffPkg⟩
  }
  exact
    ⟨cert, xUnary, yUnary, streamXUnary, streamYUnary, toleranceUnary, classifierUnary,
      sealUnary, handoffUnary, provenancePkg, handoffPkg⟩

def CauchySequenceEquivalenceEndpointCarrier [AskSetup] [PackageSetup]
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
    CauchySequenceEquivalenceEndpointCarrier leftSeq rightSeq witness regseq realSeal transport
        route provenance nameRow bundle pkg ->
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

theorem CauchySequenceEquivalenceCarrier_regseqrat_real_handoff [AskSetup] [PackageSetup]
    {leftSeq rightSeq witness regseq realSeal transport route provenance nameRow
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceEquivalenceEndpointCarrier leftSeq rightSeq witness regseq realSeal transport
        route provenance nameRow bundle pkg ->
      Cont regseq realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory leftSeq ∧ UnaryHistory rightSeq ∧ UnaryHistory witness ∧
            UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
              Cont leftSeq rightSeq witness ∧ Cont witness regseq realSeal ∧
                Cont regseq realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier regRealEndpoint endpointPkg
  obtain ⟨leftUnary, rightUnary, witnessUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameRowUnary, leftRightWitness,
    witnessRegReal, _realTransportRoute, _routeNameProvenance, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed regseqUnary realSealUnary regRealEndpoint
  exact
    ⟨leftUnary, rightUnary, witnessUnary, regseqUnary, realSealUnary, endpointUnary,
      leftRightWitness, witnessRegReal, regRealEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.CauchySequenceEquivalenceUp
