import BEDC.Derived.LocatedInfimumUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumWindowInduction [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance localName
      windowRead transportedRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        localName bundle pkg ->
      Cont window regseq windowRead ->
        Cont windowRead transport transportedRead ->
          Cont transportedRead route replayRead ->
            Cont replayRead localName namedRead ->
              PkgSig bundle provenance pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row window ∨ hsame row regseq ∨ hsame row windowRead ∨
                        hsame row transportedRead ∨ hsame row replayRead ∨
                          hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont window regseq windowRead ∧
                        Cont windowRead transport transportedRead ∧
                          Cont transportedRead route replayRead ∧
                            Cont replayRead localName namedRead ∧
                              PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory transportedRead ∧
                    UnaryHistory replayRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: LocatedInfimumCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier windowRoute transportRoute replayRoute namedRoute provenancePkg
  obtain ⟨_familyUnary, _lowerUnary, _greatestUnary, windowUnary, regseqUnary,
    _realSealUnary, transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _regseqRealSealRoute, _carrierProvenancePkg, _localNamePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary regseqUnary windowRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed windowReadUnary transportUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary routeUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row regseq ∨ hsame row windowRead ∨
              hsame row transportedRead ∨ hsame row replayRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window regseq windowRead ∧
              Cont windowRead transport transportedRead ∧
                Cont transportedRead route replayRead ∧ Cont replayRead localName namedRead ∧
                  PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, transportRoute, replayRoute, namedRoute, provenancePkg⟩
  }
  exact ⟨cert, windowReadUnary, transportedUnary, replayUnary, namedUnary⟩

end BEDC.Derived.LocatedInfimumUp
