import BEDC.Derived.RealRationalApproximationUp.WindowExtraction
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealRationalApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealRationalApproximationRealSealHandoff [AskSetup] [PackageSetup]
    {R Q D S G A H C P N windowRead readbackRead toleranceRead ledgerRead approximantRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory S ->
        UnaryHistory G ->
          UnaryHistory D ->
            UnaryHistory A ->
              UnaryHistory Q ->
                Cont R S windowRead ->
                  Cont windowRead G readbackRead ->
                    Cont readbackRead D toleranceRead ->
                      Cont toleranceRead A ledgerRead ->
                        Cont ledgerRead Q approximantRead ->
                          Cont approximantRead R sealRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle sealRead pkg ->
                                SemanticNameCert
                                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row Q ∨ hsame row D ∨ hsame row S ∨
                                      hsame row G ∨ hsame row A ∨ hsame row R ∨
                                        hsame row sealRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont approximantRead R sealRead ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
                                  hsame ∧ UnaryHistory approximantRead ∧
                                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro realUnary streamUnary readbackUnary toleranceUnary ledgerUnary approximantUnary
    windowCont readbackCont toleranceCont ledgerCont approximantCont sealCont provenancePkg
    sealPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed realUnary streamUnary windowCont
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary readbackUnary readbackCont
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackReadUnary toleranceUnary toleranceCont
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed toleranceReadUnary ledgerUnary ledgerCont
  have approximantReadUnary : UnaryHistory approximantRead :=
    unary_cont_closed ledgerReadUnary approximantUnary approximantCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approximantReadUnary realUnary sealCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Q ∨ hsame row D ∨ hsame row S ∨ hsame row G ∨ hsame row A ∨
            hsame row R ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont approximantRead R sealRead ∧ PkgSig bundle P pkg ∧
            PkgSig bundle sealRead pkg)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    · intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    · intro row source
      exact ⟨source.right, sealCont, provenancePkg, sealPkg⟩
  exact ⟨cert, approximantReadUnary, sealUnary⟩

end BEDC.Derived.RealRationalApproximationUp
