import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedInfimumCarrier [AskSetup] [PackageSetup]
    (family lower greatest window regseq realSeal transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory family ∧ UnaryHistory lower ∧ UnaryHistory greatest ∧ UnaryHistory window ∧
    UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont regseq realSeal route ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem LocatedInfimumLedgerExactness [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name observation :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg ->
      Cont lower greatest observation ->
        PkgSig bundle observation pkg ->
          UnaryHistory family ∧ UnaryHistory lower ∧ UnaryHistory greatest ∧
            UnaryHistory observation ∧ Cont lower greatest observation ∧
              Cont regseq realSeal route ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle observation pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lowerGreatestObservation observationPkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, _windowUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    regseqRealSealRoute, provenancePkg, _namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed lowerUnary greatestUnary lowerGreatestObservation
  exact
    ⟨familyUnary, lowerUnary, greatestUnary, observationUnary, lowerGreatestObservation,
      regseqRealSealRoute, provenancePkg, observationPkg⟩

theorem LocatedInfimumWindowLedgerCoverage [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name windowRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route
        provenance name bundle pkg →
      Cont window regseq windowRead →
      Cont windowRead realSeal sealRead →
      PkgSig bundle provenance pkg →
      PkgSig bundle sealRead pkg →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row window ∨ hsame row regseq ∨ hsame row windowRead ∨
                hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row family ∨ hsame row lower ∨ hsame row greatest ∨ hsame row window ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row windowRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window regseq windowRead ∧
              Cont windowRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame ∧
        UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRegseq windowReadSeal provenancePkg sealPkg
  obtain ⟨_familyUnary, _lowerUnary, _greatestUnary, windowUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _regseqRealSealRoute, _carrierProvenancePkg, _namePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary regseqUnary windowRegseq
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary realSealUnary windowReadSeal
  have windowSource :
      (fun row : BHist =>
        (hsame row window ∨ hsame row regseq ∨ hsame row windowRead ∨
            hsame row sealRead) ∧
          UnaryHistory row) window := by
    exact ⟨Or.inl (hsame_refl window), windowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row window ∨ hsame row regseq ∨ hsame row windowRead ∨
                hsame row sealRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row family ∨ hsame row lower ∨ hsame row greatest ∨ hsame row window ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row windowRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont window regseq windowRead ∧
              Cont windowRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro window windowSource
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameWindow =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameWindow)))
      | inr rest₁ =>
          cases rest₁ with
          | inl sameRegseq =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRegseq))))
          | inr rest₂ =>
              cases rest₂ with
              | inl sameWindowRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameWindowRead))))))
              | inr sameSealRead =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr sameSealRead))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRegseq, windowReadSeal, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, windowReadUnary, sealReadUnary⟩

theorem LocatedInfimumSupremumDualExactness [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name supremumRead
      familyRead lowerRead sealRead exactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg ->
      Cont family window supremumRead ->
        Cont supremumRead lower familyRead ->
          Cont familyRead greatest lowerRead ->
            Cont lowerRead realSeal sealRead ->
              Cont sealRead name exactRead ->
                PkgSig bundle exactRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row family ∨ hsame row lower ∨ hsame row greatest ∨
                          hsame row window ∨ hsame row regseq ∨ hsame row realSeal ∨
                            hsame row sealRead ∨ hsame row exactRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont family window supremumRead ∧
                          Cont supremumRead lower familyRead ∧
                            Cont familyRead greatest lowerRead ∧
                              Cont lowerRead realSeal sealRead ∧
                                Cont sealRead name exactRead ∧
                                  PkgSig bundle exactRead pkg)
                      hsame ∧
                    UnaryHistory exactRead := by
  -- BEDC touchpoint anchor: LocatedInfimumCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier familyWindow supremumLower familyGreatest lowerReal sealName exactPkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _regseqRealSealRoute, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed familyUnary windowUnary familyWindow
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed supremumUnary lowerUnary supremumLower
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed familyReadUnary greatestUnary familyGreatest
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerReadUnary realSealUnary lowerReal
  have exactReadUnary : UnaryHistory exactRead :=
    unary_cont_closed sealReadUnary nameUnary sealName
  have sourceExact :
      (fun row : BHist => hsame row exactRead ∧ UnaryHistory row) exactRead := by
    exact ⟨hsame_refl exactRead, exactReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row family ∨ hsame row lower ∨ hsame row greatest ∨ hsame row window ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row sealRead ∨
                hsame row exactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont family window supremumRead ∧
              Cont supremumRead lower familyRead ∧ Cont familyRead greatest lowerRead ∧
                Cont lowerRead realSeal sealRead ∧ Cont sealRead name exactRead ∧
                  PkgSig bundle exactRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exactRead sourceExact
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, familyWindow, supremumLower, familyGreatest, lowerReal,
          sealName, exactPkg⟩
  }
  exact ⟨cert, exactReadUnary⟩

end BEDC.Derived.LocatedInfimumUp
