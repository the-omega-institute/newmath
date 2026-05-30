import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirichletKernelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DirichletKernelNameCertObligations [AskSetup] [PackageSetup]
    {window coeff circle complexSum fourier series transport replay provenance name phaseRead
      sumRead kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window →
      UnaryHistory coeff →
        UnaryHistory circle →
          UnaryHistory complexSum →
            UnaryHistory fourier →
              UnaryHistory series →
                UnaryHistory transport →
                  UnaryHistory replay →
                    UnaryHistory provenance →
                      UnaryHistory name →
                        Cont window coeff phaseRead →
                          Cont phaseRead circle sumRead →
                            Cont sumRead complexSum kernelRead →
                              Cont transport replay provenance →
                                PkgSig bundle provenance pkg →
                                  PkgSig bundle name pkg →
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row window ∨ hsame row coeff ∨
                                            hsame row circle ∨ hsame row complexSum ∨
                                              hsame row fourier ∨ hsame row series ∨
                                                hsame row kernelRead) ∧
                                          UnaryHistory row)
                                      (fun _row : BHist =>
                                        Cont window coeff phaseRead ∧
                                          Cont phaseRead circle sumRead ∧
                                            Cont sumRead complexSum kernelRead ∧
                                              Cont transport replay provenance ∧
                                                PkgSig bundle provenance pkg)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle provenance pkg)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro windowUnary coeffUnary circleUnary complexSumUnary fourierUnary seriesUnary
    _transportUnary _replayUnary _provenanceUnary _nameUnary windowCoeff phaseCircle
    sumComplex transportReplay provenancePkg _namePkg
  have phaseReadUnary : UnaryHistory phaseRead :=
    unary_cont_closed windowUnary coeffUnary windowCoeff
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed phaseReadUnary circleUnary phaseCircle
  have kernelReadUnary : UnaryHistory kernelRead :=
    unary_cont_closed sumReadUnary complexSumUnary sumComplex
  have sourceWindow :
      (fun row : BHist =>
        (hsame row window ∨ hsame row coeff ∨ hsame row circle ∨ hsame row complexSum ∨
            hsame row fourier ∨ hsame row series ∨ hsame row kernelRead) ∧
          UnaryHistory row) window := by
    exact ⟨Or.inl (hsame_refl window), windowUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro window sourceWindow
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
        intro row other sameRows source
        cases source with
        | intro sourceRows sourceUnary =>
            constructor
            · cases sourceRows with
              | inl sameWindow =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)
              | inr rest =>
                  cases rest with
                  | inl sameCoeff =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameCoeff))
                  | inr rest =>
                      cases rest with
                      | inl sameCircle =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameCircle)))
                      | inr rest =>
                          cases rest with
                          | inl sameComplex =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameComplex))))
                          | inr rest =>
                              cases rest with
                              | inl sameFourier =>
                                  exact
                                    Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                      Or.inl (hsame_trans (hsame_symm sameRows) sameFourier)
                              | inr rest =>
                                  cases rest with
                                  | inl sameSeries =>
                                      exact
                                        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                          Or.inr <|
                                            Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameSeries)
                                  | inr sameKernel =>
                                      exact
                                        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                          Or.inr <| Or.inr <|
                                            hsame_trans (hsame_symm sameRows) sameKernel
            · exact unary_transport sourceUnary sameRows
    }
    pattern_sound := by
      intro _row _source
      exact ⟨windowCoeff, phaseCircle, sumComplex, transportReplay, provenancePkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }

end BEDC.Derived.DirichletKernelUp
