import BEDC.Derived.LimsupLiminfGapUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LimsupLiminfGapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LimsupLiminfGapCarrier [AskSetup] [PackageSetup]
    (source lowerEndpoint upperEndpoint dyadic rationalRead endpoint transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory source ∧ UnaryHistory lowerEndpoint ∧ UnaryHistory upperEndpoint ∧
    UnaryHistory dyadic ∧ UnaryHistory rationalRead ∧ UnaryHistory endpoint ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont source lowerEndpoint upperEndpoint ∧
          Cont dyadic rationalRead endpoint ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem LimsupLiminfGapEndpointRoute [AskSetup] [PackageSetup]
    {source lowerEndpoint upperEndpoint dyadic rationalRead endpoint transport replay
      provenance localName endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LimsupLiminfGapCarrier source lowerEndpoint upperEndpoint dyadic rationalRead endpoint
        transport replay provenance localName bundle pkg →
      Cont lowerEndpoint upperEndpoint dyadic →
        Cont dyadic rationalRead endpointRead →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row lowerEndpoint ∨ hsame row upperEndpoint ∨
                    hsame row dyadic ∨ hsame row rationalRead ∨ hsame row endpointRead)
                (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row endpointRead)
                hsame ∧
              UnaryHistory endpointRead ∧ Cont lowerEndpoint upperEndpoint dyadic ∧
                Cont dyadic rationalRead endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier endpointWindow dyadicRational provenancePkg
  have dyadicUnary : UnaryHistory dyadic :=
    carrier.right.right.right.left
  have rationalUnary : UnaryHistory rationalRead :=
    carrier.right.right.right.right.left
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed dyadicUnary rationalUnary dyadicRational
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row lowerEndpoint ∨ hsame row upperEndpoint ∨
              hsame row dyadic ∨ hsame row rationalRead ∨ hsame row endpointRead)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row endpointRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.left⟩
  }
  exact ⟨cert, endpointReadUnary, endpointWindow, dyadicRational⟩

theorem LimsupLiminfGapNameCertObligations [AskSetup] [PackageSetup]
    {source lowerEndpoint upperEndpoint dyadic rationalRead endpoint transport replay
      provenance localName endpointRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LimsupLiminfGapCarrier source lowerEndpoint upperEndpoint dyadic rationalRead endpoint
        transport replay provenance localName bundle pkg →
      Cont lowerEndpoint upperEndpoint dyadic →
      Cont dyadic rationalRead endpointRead →
      Cont replay provenance localRead →
      PkgSig bundle provenance pkg →
      PkgSig bundle localName pkg →
      PkgSig bundle endpointRead pkg →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row source ∨ hsame row lowerEndpoint ∨ hsame row upperEndpoint ∨
                hsame row dyadic ∨ hsame row rationalRead ∨ hsame row endpointRead ∨
                  hsame row localRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row lowerEndpoint ∨ hsame row upperEndpoint ∨
              hsame row dyadic ∨ hsame row rationalRead ∨ hsame row endpointRead ∨
                hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerEndpoint upperEndpoint dyadic ∧
              Cont dyadic rationalRead endpointRead ∧ Cont replay provenance localRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle endpointRead pkg)
          hsame ∧
        UnaryHistory endpointRead ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: LimsupLiminfGapCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier endpointWindow dyadicRational replayProvenance provenancePkg localNamePkg
    endpointReadPkg
  have sourceUnary : UnaryHistory source := carrier.left
  have lowerUnary : UnaryHistory lowerEndpoint := carrier.right.left
  have upperUnary : UnaryHistory upperEndpoint := carrier.right.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.right.left
  have rationalUnary : UnaryHistory rationalRead := carrier.right.right.right.right.left
  have replayUnary : UnaryHistory replay :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.right.right.left
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed dyadicUnary rationalUnary dyadicRational
  have localReadUnary : UnaryHistory localRead :=
    unary_cont_closed replayUnary provenanceUnary replayProvenance
  have sourceWitness :
      (fun row : BHist =>
        (hsame row source ∨ hsame row lowerEndpoint ∨ hsame row upperEndpoint ∨
            hsame row dyadic ∨ hsame row rationalRead ∨ hsame row endpointRead ∨
              hsame row localRead) ∧
          UnaryHistory row) source := by
    exact ⟨Or.inl (hsame_refl source), sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row source ∨ hsame row lowerEndpoint ∨ hsame row upperEndpoint ∨
                hsame row dyadic ∨ hsame row rationalRead ∨ hsame row endpointRead ∨
                  hsame row localRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row lowerEndpoint ∨ hsame row upperEndpoint ∨
              hsame row dyadic ∨ hsame row rationalRead ∨ hsame row endpointRead ∨
                hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerEndpoint upperEndpoint dyadic ∧
              Cont dyadic rationalRead endpointRead ∧ Cont replay provenance localRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro source sourceWitness
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
        intro _row _other sameRows sourceData
        constructor
        · cases sourceData.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr rest₁ =>
              cases rest₁ with
              | inl sameLower =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLower))
              | inr rest₂ =>
                  cases rest₂ with
                  | inl sameUpper =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameUpper)))
                  | inr rest₃ =>
                      cases rest₃ with
                      | inl sameDyadic =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic))))
                      | inr rest₄ =>
                          cases rest₄ with
                          | inl sameRational =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows)
                                            sameRational)))))
                          | inr rest₅ =>
                              cases rest₅ with
                              | inl sameEndpointRead =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm sameRows)
                                                  sameEndpointRead))))))
                              | inr sameLocalRead =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (hsame_trans (hsame_symm sameRows)
                                                  sameLocalRead))))))
        · exact unary_transport sourceData.right sameRows
    }
    pattern_sound := by
      intro _row sourceData
      exact sourceData.left
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, endpointWindow, dyadicRational, replayProvenance,
          provenancePkg, localNamePkg, endpointReadPkg⟩
  }
  exact ⟨cert, endpointReadUnary, localReadUnary⟩

end BEDC.Derived.LimsupLiminfGapUp
