import BEDC.Derived.DiniUniformConvergenceUp.NameCertObligations

namespace BEDC.Derived.DiniUniformConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiniUniformConvergenceCarrier_monotone_family_exhaustion [AskSetup] [PackageSetup]
    {K T F M W R E H C P N familyRead windowRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiniUniformConvergenceCarrier K T F M W R E H C P N bundle pkg →
      Cont K T F →
        Cont F M familyRead →
          Cont familyRead W windowRead →
            Cont windowRead R readbackRead →
              Cont readbackRead E sealRead →
                PkgSig bundle P pkg →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K ∨ hsame row T ∨ hsame row F ∨ hsame row M ∨
                            hsame row W ∨ hsame row R ∨ hsame row E ∨
                              hsame row familyRead ∨ hsame row windowRead ∨
                                hsame row readbackRead ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont K T F ∧ Cont F M familyRead ∧
                            Cont familyRead W windowRead ∧
                              Cont windowRead R readbackRead ∧
                                Cont readbackRead E sealRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory familyRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier compactFiniteNet familyModulus familyWindow windowReadback readbackSeal
    provenancePkg namePkg
  have compactUnary : UnaryHistory K := carrier.left
  have finiteNetUnary : UnaryHistory T := carrier.right.left
  have modulusUnary : UnaryHistory M := carrier.right.right.right.left
  have windowUnary : UnaryHistory W := carrier.right.right.right.right.left
  have readbackUnary : UnaryHistory R := carrier.right.right.right.right.right.left
  have sealUnary : UnaryHistory E := carrier.right.right.right.right.right.right.left
  have familyUnary : UnaryHistory F :=
    unary_cont_closed compactUnary finiteNetUnary compactFiniteNet
  have familyReadUnary : UnaryHistory familyRead :=
    unary_cont_closed familyUnary modulusUnary familyModulus
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed familyReadUnary windowUnary familyWindow
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary readbackUnary windowReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealUnary readbackSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row T ∨ hsame row F ∨ hsame row M ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row familyRead ∨
                hsame row windowRead ∨ hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K T F ∧ Cont F M familyRead ∧
              Cont familyRead W windowRead ∧ Cont windowRead R readbackRead ∧
                Cont readbackRead E sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactFiniteNet, familyModulus, familyWindow, windowReadback,
          readbackSeal, provenancePkg, namePkg⟩
  }
  exact ⟨cert, familyReadUnary, windowReadUnary, readbackReadUnary, sealReadUnary⟩

end BEDC.Derived.DiniUniformConvergenceUp
