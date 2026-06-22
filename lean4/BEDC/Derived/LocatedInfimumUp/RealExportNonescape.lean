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

theorem LocatedInfimumRealExportNonescape [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name familyRead
      lowerRead witnessRead windowRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg ->
      Cont family lower familyRead ->
        Cont familyRead greatest lowerRead ->
          Cont lowerRead window witnessRead ->
            Cont witnessRead regseq windowRead ->
              Cont windowRead realSeal realRead ->
                PkgSig bundle realRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row family ∨ hsame row lower ∨ hsame row greatest ∨
                          hsame row window ∨ hsame row regseq ∨ hsame row realSeal ∨
                            hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont witnessRead regseq windowRead ∧
                          Cont windowRead realSeal realRead ∧ PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory familyRead ∧ UnaryHistory lowerRead ∧
                      UnaryHistory witnessRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: LocatedInfimumCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier familyLower lowerGreatest witnessWindow windowRegseq realExport realPkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _regseqRealSealRoute, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed familyUnary lowerUnary familyLower
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed familyReadUnary greatestUnary lowerGreatest
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed lowerReadUnary windowUnary witnessWindow
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed witnessReadUnary regseqUnary windowRegseq
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed windowReadUnary realSealUnary realExport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row family ∨ hsame row lower ∨ hsame row greatest ∨ hsame row window ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont witnessRead regseq windowRead ∧
              Cont windowRead realSeal realRead ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact ⟨source.right, windowRegseq, realExport, realPkg⟩
  }
  exact
    ⟨cert, familyReadUnary, lowerReadUnary, witnessReadUnary, windowReadUnary,
      realReadUnary⟩

end BEDC.Derived.LocatedInfimumUp
