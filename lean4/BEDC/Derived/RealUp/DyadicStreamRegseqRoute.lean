import BEDC.Derived.RealUp.L10DependencyLattice
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealDyadicStreamRegseqRoute [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport provenance localName sourceRoute streamRoute
      regseqRoute sealRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic → UnaryHistory stream → UnaryHistory regseq → UnaryHistory sealRow →
      UnaryHistory transport → UnaryHistory provenance → UnaryHistory localName →
        Cont dyadic stream sourceRoute → Cont sourceRoute regseq streamRoute →
          Cont streamRoute sealRow regseqRoute → Cont regseqRoute transport sealRoute →
            PkgSig bundle provenance pkg → PkgSig bundle sealRoute pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceRoute ∨ hsame row streamRoute ∨
                        hsame row regseqRoute ∨ hsame row sealRoute) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row sealRow ∨ hsame row transport ∨ hsame row sourceRoute ∨
                        hsame row streamRoute ∨ hsame row regseqRoute ∨
                          hsame row sealRoute)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont dyadic stream sourceRoute ∧
                      Cont sourceRoute regseq streamRoute ∧
                        Cont streamRoute sealRow regseqRoute ∧
                          Cont regseqRoute transport sealRoute ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle sealRoute pkg)
                  hsame ∧
                UnaryHistory sourceRoute ∧ UnaryHistory streamRoute ∧
                  UnaryHistory regseqRoute ∧ UnaryHistory sealRoute := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary _provenanceUnary
    _localNameUnary dyadicStream sourceRegseq streamSeal regseqTransport provenancePkg
    sealPkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed dyadicUnary streamUnary dyadicStream
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseq
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed streamRouteUnary sealUnary streamSeal
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regseqRouteUnary transportUnary regseqTransport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceRoute ∨ hsame row streamRoute ∨ hsame row regseqRoute ∨
                hsame row sealRoute) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row sealRow ∨
              hsame row transport ∨ hsame row sourceRoute ∨ hsame row streamRoute ∨
                hsame row regseqRoute ∨ hsame row sealRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream sourceRoute ∧
              Cont sourceRoute regseq streamRoute ∧ Cont streamRoute sealRow regseqRoute ∧
                Cont regseqRoute transport sealRoute ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRoute pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRoute ⟨Or.inl (hsame_refl sourceRoute), sourceUnary⟩
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
        constructor
        · cases source.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr tail =>
              cases tail with
              | inl sameStream =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameStream))
              | inr tail =>
                  cases tail with
                  | inl sameRegseq =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRegseq)))
                  | inr sameSeal =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inl sameSource)))))
      | inr tail =>
          cases tail with
          | inl sameStream =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl sameStream))))))
          | inr tail =>
              cases tail with
              | inl sameRegseq =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl sameRegseq)))))))
              | inr sameSeal =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr sameSeal)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicStream, sourceRegseq, streamSeal, regseqTransport, provenancePkg,
          sealPkg⟩
  }
  exact ⟨cert, sourceUnary, streamRouteUnary, regseqRouteUnary, sealRouteUnary⟩

end BEDC.Derived.RealUp
