import BEDC.Derived.LocatedInfimumUp

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumObligationTailLattice [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name lowerCutRead
      tailRead regseqRead sealRead latticeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route
        provenance name bundle pkg →
      Cont lower greatest lowerCutRead →
        Cont lowerCutRead window tailRead →
          Cont tailRead regseq regseqRead →
            Cont regseqRead realSeal sealRead →
              Cont sealRead name latticeRead →
                PkgSig bundle latticeRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row latticeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row lowerCutRead ∨ hsame row tailRead ∨
                          hsame row regseqRead ∨ hsame row sealRead ∨
                            hsame row latticeRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle latticeRead pkg)
                      hsame ∧
                    UnaryHistory lowerCutRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory regseqRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory latticeRead := by
  -- BEDC touchpoint anchor: LocatedInfimumCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier lowerGreatestRead lowerCutWindowTail tailRegseqRead
    regseqRealSealRead sealNameLattice latticePkg
  obtain ⟨_familyUnary, lowerUnary, greatestUnary, windowUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    _regseqRealSealRoute, _provenancePkg, _namePkg⟩ := carrier
  have lowerCutUnary : UnaryHistory lowerCutRead :=
    unary_cont_closed lowerUnary greatestUnary lowerGreatestRead
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed lowerCutUnary windowUnary lowerCutWindowTail
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed tailUnary regseqUnary tailRegseqRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary regseqRealSealRead
  have latticeUnary : UnaryHistory latticeRead :=
    unary_cont_closed sealReadUnary nameUnary sealNameLattice
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row latticeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lowerCutRead ∨ hsame row tailRead ∨ hsame row regseqRead ∨
              hsame row sealRead ∨ hsame row latticeRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle latticeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro latticeRead ⟨hsame_refl latticeRead, latticeUnary⟩
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
      exact ⟨source.right, latticePkg⟩
  }
  exact
    ⟨cert, lowerCutUnary, tailUnary, regseqReadUnary, sealReadUnary, latticeUnary⟩

end BEDC.Derived.LocatedInfimumUp
