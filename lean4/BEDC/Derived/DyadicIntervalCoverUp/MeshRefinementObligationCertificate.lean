import BEDC.Derived.DyadicIntervalCoverUp.MeshRefinementObligation

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverMeshRefinementObligationCertificate [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N refinedEndpoint refinedCover refinedWindow refinedSeal
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U refinedEndpoint →
        Cont M R refinedCover →
          Cont W Q refinedWindow →
            Cont refinedWindow A refinedSeal →
              Cont refinedCover refinedSeal namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                          hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L U refinedEndpoint ∧
                          Cont M R refinedCover ∧ Cont W Q refinedWindow ∧
                            Cont refinedWindow A refinedSeal ∧
                              Cont refinedCover refinedSeal namedRead ∧
                                PkgSig bundle namedRead pkg)
                      hsame ∧ UnaryHistory refinedEndpoint ∧ UnaryHistory refinedCover ∧
                    UnaryHistory refinedWindow ∧ UnaryHistory refinedSeal ∧
                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface endpointCont coverCont windowCont sealCont nameCont namePkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory refinedEndpoint :=
    unary_cont_closed lUnary uUnary endpointCont
  have coverUnary : UnaryHistory refinedCover :=
    unary_cont_closed mUnary rUnary coverCont
  have windowUnary : UnaryHistory refinedWindow :=
    unary_cont_closed wUnary qUnary windowCont
  have sealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed windowUnary aUnary sealCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed coverUnary sealUnary nameCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U refinedEndpoint ∧ Cont M R refinedCover ∧
              Cont W Q refinedWindow ∧ Cont refinedWindow A refinedSeal ∧
                Cont refinedCover refinedSeal namedRead ∧ PkgSig bundle namedRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointCont, coverCont, windowCont, sealCont, nameCont, namePkg⟩
  }
  exact ⟨cert, endpointUnary, coverUnary, windowUnary, sealUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
