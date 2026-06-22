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

theorem LocatedInfimumSupremumDualRoute [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name supremumRead
      familyRead lowerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg ->
      Cont family window supremumRead ->
        Cont supremumRead lower familyRead ->
          Cont familyRead greatest lowerRead ->
            Cont lowerRead realSeal sealRead ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row family ∨ hsame row lower ∨ hsame row greatest ∨
                        hsame row window ∨ hsame row regseq ∨ hsame row realSeal ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont family window supremumRead ∧
                        Cont supremumRead lower familyRead ∧
                          Cont familyRead greatest lowerRead ∧
                            Cont lowerRead realSeal sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory supremumRead ∧ UnaryHistory familyRead ∧
                    UnaryHistory lowerRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: LocatedInfimumCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier familyWindow supremumLower familyGreatest lowerReal sealPkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _regseqRealSealRoute, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed familyUnary windowUnary familyWindow
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed supremumUnary lowerUnary supremumLower
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed familyReadUnary greatestUnary familyGreatest
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerReadUnary realSealUnary lowerReal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row family ∨ hsame row lower ∨ hsame row greatest ∨ hsame row window ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont family window supremumRead ∧
              Cont supremumRead lower familyRead ∧ Cont familyRead greatest lowerRead ∧
                Cont lowerRead realSeal sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, familyWindow, supremumLower, familyGreatest, lowerReal, sealPkg⟩
  }
  exact ⟨cert, supremumUnary, familyReadUnary, lowerReadUnary, sealReadUnary⟩

end BEDC.Derived.LocatedInfimumUp
